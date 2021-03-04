/* ---------------------------------------------------------------------------------------
 *      Notify-bibi Symbolic-Emulation-Engine project
 *      Copyright (c) 2019 Microsoft Corporation by notify-bibi@github, 2496424084@qq.com
 *      ALL RIGHTS RESERVED.
 *
 *      快速的（采用高速的扩展指令）将page中的符号(ast)和真值(numreal)进行合并返回和拆分存入。
        核心代码，对效率十分重要。cp必究
 *
 * ---------------------------------------------------------------------------------------
 */

#define UNDEFREG
#include "register.h"

class Translate {
    z3::vcontext& m_toctx;
    Z3_ast m_ast;
public:
    inline Translate(z3::vcontext& ctx, z3::vcontext& toctx, Z3_ast s) :
        m_toctx(toctx)
    {
#if !defined(CLOSECNW)&&!defined(USECNWNOAST)
        spin_unique_lock lock(ctx);
#endif
        m_ast = Z3_translate(ctx, s, toctx);
        Z3_inc_ref(toctx, m_ast);
    }

    inline operator Z3_ast() {
        return m_ast;
    }

    inline ~Translate() {
        Z3_dec_ref(m_toctx, m_ast);
    }

};


namespace TR {
    Symbolic::Symbolic(z3::vcontext& ctx, UInt size)
        : m_ctx(ctx), m_size(size) 
    {
        memset(m_fastindex, 0, size);
    }

    TR::Symbolic::Symbolic(z3::vcontext& ctx, TR::Symbolic* father)
        : m_ctx(ctx), m_size(father->m_size)
    {
        memcpy(m_fastindex, father->m_fastindex, m_size);
        memset(m_fastindex + m_size, 0, 32);

        HASH_MAP<Int, Z3_ast>& fast = father->m_ast.m_mem;
        auto it_end = fast.end();
        for (auto it = fast.begin(); it != it_end; it++) {
            if (m_fastindex[it->first] == 1) {
                Z3_ast translate_ast = Translate(father->m_ctx, m_ctx, it->second);
                m_ast[it->first] = translate_ast;
                vassert(translate_ast != NULL);
                Z3_inc_ref(m_ctx, translate_ast);
            }
        }
    }

    Symbolic::~Symbolic()
    {
        int _pcur = m_size - 1;
        int N;
        for (; _pcur > 0; ) {

            if (clzll(N, ((ULong*)(m_fastindex))[_pcur >> 3] & fastMaskBI1(_pcur % 8))) {
                N = 63 - N;
                _pcur = ALIGN(_pcur, 8) + (N >> 3);
                _pcur = _pcur - m_fastindex[_pcur] + 1;
                Z3_dec_ref(m_ctx, m_ast[_pcur]);
                _pcur--;
            }
            else {
                _pcur = ALIGN(_pcur - 8, 8) + 7;
            }
        };
    }
    Symbolic* Symbolic::mk_Symbolic(z3::vcontext& ctx, UInt size)
    {
        UChar* ptr = new UChar[sizeof(Symbolic) + size] ;
        new (ptr) Symbolic(ctx, size);
        return reinterpret_cast<Symbolic*>(ptr);
    }
    Symbolic* Symbolic::mk_Symbolic(z3::vcontext& ctx, Symbolic* father)
    {
        UChar* ptr = new UChar[sizeof(Symbolic) + father->m_size];
        new (ptr) Symbolic(ctx, father);
        return reinterpret_cast<Symbolic*>(ptr);
    }
    void Symbolic::del_Symbolic(Symbolic* ptr)
    {
        delete ptr;
    }
};


namespace TR {



    Register::Register(z3::vcontext& ctx, UInt size) 
        : m_ctx(ctx),
        m_is_symbolic(false),
        m_symbolic(NULL),
        m_size(size)
    {
        //static_assert(offsetof(Register, m_bytes) + maxlength == sizeof(Register), "err");
    }

    Register::Register(Register& father_regs, z3::vcontext& ctx) 
        : m_ctx(ctx),
        m_is_symbolic(father_regs.m_is_symbolic),
        m_symbolic(father_regs.m_symbolic ? Symbolic::mk_Symbolic(m_ctx, father_regs.m_symbolic) : NULL),
        m_size(father_regs.m_size)
    {
        memcpy(m_bytes, father_regs.m_bytes, m_size);
    }


    void Register::mk_Symbolic()
    {
        if (!m_is_symbolic) {
            m_is_symbolic = true;
            m_symbolic = Symbolic::mk_Symbolic(m_ctx, m_size);
        }
    }

    void Register::init_padding_v(Char v)
    {
        memset(m_bytes, v, m_size);
    }

    Register::~Register() {
        if (m_is_symbolic) Symbolic::del_Symbolic(m_symbolic);
    }
    Register* Register::mk_Register(z3::vcontext& ctx, UInt size)
    {
        UChar* ptr = new UChar[sizeof(Register) + size];
        new (ptr) Register(ctx, size);
        return reinterpret_cast<Register*>(ptr);
    }
    Register* Register::mk_Register(Register& father_regs, z3::vcontext& ctx)
    {
        UChar* ptr = new UChar[sizeof(Register) + father_regs.m_size];
        new (ptr) Register(father_regs, ctx);
        return reinterpret_cast<Register*>(ptr);
    }
    void Register::del_Register(Register* ptr)
    {
        delete ptr;
    }
    ;

    void setfast(void* fast_ptr, UInt __nbytes) {
        class RegisterStatic final {
            __m256i data_A[33];
            __m256i data_B[33];
        public:
            RegisterStatic() {
                __m256i* m32_fast = reinterpret_cast<__m256i*>(&data_A);
                __m256i* m32_mask_reverse = reinterpret_cast<__m256i*>(&data_B);
                const __m256i m32 = _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19);
                for (int i = 0; i <= 32; i++) {
                    m32_fast[i] = m32;
                    for (int j = i; j <= 32; j++) {
                        M256i(m32_fast[i]).m256i_i8[j] = 0;
                    }
                    m32_mask_reverse[i] = _mm256_setzero_si256();
                    memset(&M256i(m32_mask_reverse[i]).m256i_i8[i], -1ul, 32 - i);
                }
            }
            const inline __m256i* mask_ptr() const { return reinterpret_cast<const __m256i*>(&data_A); }
            const inline __m256i* re_mask_ptr() const { return reinterpret_cast<const __m256i*>(&data_B); }
        };
        static const RegisterStatic table;

        if ((__nbytes) <= 8) {
            if ((__nbytes) == 8) {
                SET8(fast_ptr, 0x0807060504030201);
            }
            else {
#if 0
                __asm__
                (
                    "mov %[nbytes],%%cl;\n\t"
                    "shl $3,%%rcx;\n\t"
                    "mov %[fast],%%rax;\n\t"
                    "shr %%cl,%%rax;\n\t"
                    "shl %%cl,%%rax;\n\t"
                    "mov $0x0807060504030201,%%rbx;\n\t"
                    "sub $65,%%cl;\n\t"
                    "not %%cl;\n\t"
                    "shl %%cl,%%rbx;\n\t"
                    "shr %%cl,%%rbx;\n\t"
                    "or %%rbx,%%rax;\n\t"
                    "mov %%rax,%[out];\n\t"
                    :
                [out] "=r"(GET8((fast_ptr)))
                    :
                    [fast] "r"(GET8((fast_ptr))), [nbytes] "r"((UChar)(__nbytes))
                    :
                    "rbx", "rax", "rcx" /* clobber */
                    );
#else
                UChar sl = (__nbytes << 3);
                ULong res = GET8(fast_ptr) >> sl << sl;
                GET8(fast_ptr) = (0x0807060504030201 << (~(sl - 65)) >> (~(sl - 65))) | res;
#endif
            }
        }
        else if ((__nbytes) <= 16) {
            _mm_store_si128(
                (__m128i*)(fast_ptr),
                _mm_or_si128(
                    _mm_and_si128(
                        GET16((fast_ptr)),
                        GET16(&table.re_mask_ptr()[__nbytes])
                    ),
                    GET16(&table.mask_ptr()[__nbytes])
                )
            );
        }
        else {
            _mm256_store_si256(
                (__m256i*)(fast_ptr),
                _mm256_or_si256(
                    _mm256_and_si256(
                        GET32((fast_ptr)),
                        table.re_mask_ptr()[__nbytes]
                    ),
                    table.mask_ptr()[__nbytes]
                )
            );
        }
    }


    sv::tval Register::Iex_Get(UInt offset, IRType ty)
    {
        switch (ty) {
#define lazydef(vectype,nbit)                                \
    case Ity_##vectype##nbit:                                \
        return     get<Ity_##vectype##nbit>(offset);
            lazydef(I, 8);
            lazydef(I, 16);
            lazydef(F, 32);
            lazydef(I, 32);
            lazydef(F, 64);
            lazydef(I, 64);
            lazydef(V, 128);
            lazydef(I, 128);
            lazydef(V, 256);
#undef lazydef
        default:
            VPANIC("tIRType");
        }
        return sv::tval();
    }

    sv::tval Register::Iex_Get(UInt offset, IRType ty, z3::vcontext& ctx)
    {
        switch (ty) {
#define lazydef(vectype,nbit)                                   \
    case Ity_##vectype##nbit:                                   \
        return     get<Ity_##vectype##nbit>(offset, ctx);
            lazydef(I, 8);
            lazydef(I, 16);
            lazydef(F, 32);
            lazydef(I, 32);
            lazydef(F, 64);
            lazydef(I, 64);
            lazydef(V, 128);
            lazydef(I, 128);
            lazydef(V, 256);
#undef lazydef
        default:
            VPANIC("tIRType");
        }
    }

#define m_fastindex m_symbolic->ast_idx_list()
#define m_ast m_symbolic->ast_select()

    void Register::Ist_Put(UInt offset, sv::tval const& ir)
    {
        if (ir.symb()) {
            switch (ir.nbits()) {
            case 8: set(offset, ir.tos<true, 8, Z3_BV_SORT>()); break;
            case 16:set(offset, ir.tos<true, 16, Z3_BV_SORT>()); break;
            case 32:set(offset, ir.tos<true, 32, Z3_BV_SORT>()); break;
            case 64:set(offset, ir.tos<true, 64, Z3_BV_SORT>()); break;
            case 128:set(offset, ir.tos<true, 128, Z3_BV_SORT>()); break;
            case 256:set(offset, ir.tos<true, 256, Z3_BV_SORT>()); break;
            default:
                VPANIC("error");
            }
        }
        else {
            switch (ir.nbits()) {
            case 8: set(offset, (UChar)ir); break;
            case 16:set(offset, (UShort)ir); break;
            case 32:set(offset, (UInt)ir); break;
            case 64:set(offset, (ULong)ir); break;
            case 128:set(offset, (__m128i)ir); break;
            case 256:set(offset, (__m256i)ir); break;
            default:
                VPANIC("error");
            }
        }
    }

    void Register::Ist_Put(UInt offset, const void* data, UInt nbytes)
    {
        vassert(offset + nbytes <= m_size);
        if (m_is_symbolic) {
            clear(offset, nbytes);
            memset(m_fastindex + offset, 0, nbytes);
        };
        memcpy(m_bytes + offset, data, nbytes);
    }

    void Register::Ist_Put(UInt offset, Z3_ast _ast, UInt nbytes)
    {
        mk_Symbolic();
        clear(offset, nbytes);
        auto fastindex = m_fastindex + offset;
        for (unsigned i = 0; i < nbytes; i++) { fastindex[i] = i + 1; };
        m_ast[offset] = _ast;
        Z3_inc_ref(m_ctx, _ast);
    }

    sv::tval Register::Iex_Get(UInt offset, UInt nbytes)
    {
        vassert(nbytes <= 32);
        if (this->m_is_symbolic) {
            auto fastindex = m_fastindex + offset;
            auto _nbytes = nbytes;
            while (_nbytes) {
                if (_nbytes >= 8) { _nbytes -= 8; if (GET8(fastindex + _nbytes)) { goto has_sym; }; }
                else if (_nbytes >= 4) { _nbytes -= 4; if (GET4(fastindex + _nbytes)) { goto has_sym; }; }
                else if (_nbytes >= 2) { _nbytes -= 2; if (GET2(fastindex + _nbytes)) { goto has_sym; }; }
                else { _nbytes--; if (GET1(fastindex + _nbytes)) { goto has_sym; }; }
            };
        }
        return sv::tval(m_ctx, GET32(m_bytes + offset), nbytes << 3);
    has_sym:
        return sv::tval(m_ctx, TR::freg2AstSSE(nbytes, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx), Z3_BV_SORT, nbytes << 3, no_inc{});
    }

    void Register::clear(UInt org_offset, Int LEN) {
        Char length = LEN;
        char fastR = m_fastindex[org_offset + length] - 1;
        if (fastR > 0) {
            auto index = org_offset + length - fastR;
            auto sort_size = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast[index]));

            auto AstR = Z3_mk_extract(m_ctx, sort_size - 1, (fastR << 3), m_ast[index]);
            Z3_inc_ref(m_ctx, AstR);
            m_ast[org_offset + length] = AstR;
            setfast(m_fastindex + org_offset + length, (sort_size >> 3) - fastR);
            if (fastR > length) {
                auto AstL = Z3_mk_extract(m_ctx, ((fastR - length) << 3) - 1, 0, m_ast[index]);
                Z3_inc_ref(m_ctx, AstL);
                Z3_dec_ref(m_ctx, m_ast[index]);
                m_ast[index] = AstL;
                return;
            }
            else if (fastR == length) {
                Z3_dec_ref(m_ctx, m_ast[index]);
                return;
            }
            length -= fastR;
            Z3_dec_ref(m_ctx, m_ast[index]);
        }
        char fastL = m_fastindex[org_offset] - 1;
        if (fastL > 0) {
            auto index = org_offset - fastL;
            auto sort_size = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast[index])) >> 3;
            auto newAst = Z3_mk_extract(m_ctx, ((fastL) << 3) - 1, 0, m_ast[index]);
            Z3_inc_ref(m_ctx, newAst);
            Z3_dec_ref(m_ctx, m_ast[index]);
            m_ast[index] = newAst;
            org_offset += (sort_size - fastL);
            length -= (sort_size - fastL);
        }
        Int index;
        if (LEN <= 8) {
            ULong fast_index = GET8(m_fastindex + org_offset);
            while (length > 0) {
                if (clzll(index, fast_index & fastMaskB(length))) {
                    index = 63 - index;
                    index >>= 3;
                    auto fast = m_fastindex[org_offset + index] - 1;
                    length = index - fast;
                    Z3_dec_ref(m_ctx, m_ast[org_offset + length]);
                }
                else {
                    return;
                }
            }
        }
        else {
            // It's fast for CPU to reads data from aligned addresses .
            UInt _pcur = org_offset + length - 1;
            if (_pcur < org_offset)
                return;
            for (; ; ) {

                if (clzll(index, ((ULong*)(m_fastindex))[_pcur >> 3] & fastMaskBI1(_pcur % 8))) {
                    index = 63 - index;
                    _pcur = ALIGN(_pcur, 8) + (index >> 3);
                    _pcur = _pcur - m_fastindex[_pcur] + 1;
                    if (_pcur >= org_offset)
                        Z3_dec_ref(m_ctx, m_ast[_pcur]);
                    else
                        return;
                    _pcur--;
                }
                else {
                    _pcur = ALIGN(_pcur - 8, 8) + 7;
                    if (_pcur < org_offset)
                        return;
                }
            }
        }
    };

    sv::tval Register::Iex_Get(UInt offset, UInt nbytes, z3::vcontext& ctx){
        vassert(nbytes <= 32);
        if (this->m_is_symbolic) {
            auto fastindex = m_fastindex + offset;
            auto _nbytes = nbytes;
            while (_nbytes) {
                if (_nbytes >= 8) { _nbytes -= 8; if (GET8(fastindex + _nbytes)) { goto has_sym; }; }
                else if (_nbytes >= 4) { _nbytes -= 4; if (GET4(fastindex + _nbytes)) { goto has_sym; }; }
                else if (_nbytes >= 2) { _nbytes -= 2; if (GET2(fastindex + _nbytes)) { goto has_sym; }; }
                else { _nbytes--; if (GET1(fastindex + _nbytes)) { goto has_sym; }; };
            }
        }
        return sv::tval(ctx, GET32(m_bytes + offset), nbytes << 3);
    has_sym:
        return sv::tval(ctx, TR::freg2AstSSE_cov(nbytes, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx, ctx), Z3_BV_SORT, nbytes << 3, no_inc{});
    }

};
#undef m_fastindex
#undef m_ast


namespace TR {
    

    //取值函数。将多个ast和真值组合为一个ast
#ifdef USE_HASH_AST_MANAGER
    Z3_ast freg2Ast(int nbytes, UChar* r_bytes, UChar* ast_fastindex, TR::AstManager::AstManagerX&& m_ast, z3::vcontext& ctx) {
#else
    Z3_ast TR::freg2Ast(int nbytes, UChar * r_bytes, UChar * ast_fastindex, Z3_ast * m_ast, z3::vcontext & ctx) {
#endif
        vassert(nbytes <= 8);
        ULong scan = GET8(ast_fastindex);
        Z3_ast result;
        Int index;
        Z3_ast reast;
        if (clzll(index, scan & fastMask(nbytes << 3))) {
            index = 63 - index;
            auto offset = (index >> 3);
            Char relen = nbytes - offset - 1;
            auto fast = ast_fastindex[offset];
            if (relen) {
                nbytes -= relen;
                auto zsort = Z3_mk_bv_sort(ctx, relen << 3);
                Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
                reast = Z3_mk_unsigned_int64(ctx, GET8(r_bytes + nbytes), zsort);
                Z3_inc_ref(ctx, reast);
                if (fast > nbytes) {
                    Z3_ast need_extract = Z3_mk_extract(ctx, (fast << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
                    Z3_inc_ref(ctx, need_extract);
                    result = Z3_mk_concat(ctx, reast, need_extract);
                    Z3_inc_ref(ctx, result);
                    Z3_dec_ref(ctx, need_extract);
                    nbytes -= fast;
                }
                else {
                    nbytes -= fast;
                    result = Z3_mk_concat(ctx, reast, m_ast[nbytes]);
                    Z3_inc_ref(ctx, result);
                }
                Z3_dec_ref(ctx, reast);
                Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            }
            else {
                if (nbytes < fast) {
                    result = Z3_mk_extract(ctx, ((fast) << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
                    Z3_inc_ref(ctx, result);
                    return result;
                }
                if (ast_fastindex[nbytes] >> 1) {
                    result = Z3_mk_extract(ctx, (fast << 3) - 1, 0, m_ast[nbytes - fast]);
                    nbytes -= fast;
                }
                else {
                    if (nbytes == fast) {
                        Z3_inc_ref(ctx, m_ast[nbytes - fast]);
                        return m_ast[nbytes - fast];
                    }
                    else {
                        result = m_ast[nbytes - fast];
                        nbytes -= fast;
                    }
                }
                Z3_inc_ref(ctx, result);
            }
        }
        else {
            auto zsort = Z3_mk_bv_sort(ctx, nbytes << 3);
            Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            reast = Z3_mk_unsigned_int64(ctx, GET8(r_bytes), zsort);
            Z3_inc_ref(ctx, reast);
            Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            return reast;
        }
        while (nbytes > 0) {
            if (clzll(index, scan & fastMask(nbytes << 3))) {
                index = 63 - index;
                auto offset = index >> 3;
                Char relen = nbytes - offset - 1;
                auto fast = ast_fastindex[offset];
                if (relen) {
                    nbytes -= relen;
                    auto zsort = Z3_mk_bv_sort(ctx, relen << 3);
                    Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
                    reast = Z3_mk_unsigned_int64(ctx, GET8(r_bytes + nbytes), zsort);
                    Z3_inc_ref(ctx, reast);
                    Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
                    Z3_ast newresult = Z3_mk_concat(ctx, result, reast);
                    Z3_inc_ref(ctx, newresult);
                    Z3_dec_ref(ctx, result);
                    Z3_dec_ref(ctx, reast);
                    if (nbytes < fast) {
                        Z3_ast ext = Z3_mk_extract(ctx, ((fast) << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
                        Z3_inc_ref(ctx, ext);
                        Z3_ast result = Z3_mk_concat(ctx, newresult, ext);
                        Z3_inc_ref(ctx, result);
                        Z3_dec_ref(ctx, newresult);
                        Z3_dec_ref(ctx, ext);
                        return result;
                    }
                    else {
                        result = Z3_mk_concat(ctx, newresult, m_ast[nbytes - fast]);
                        Z3_inc_ref(ctx, result);
                        Z3_dec_ref(ctx, newresult);
                        nbytes -= fast;
                    }
                }
                else {
                    if (nbytes < fast) {
                        Z3_ast ext = Z3_mk_extract(ctx, ((fast) << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
                        Z3_inc_ref(ctx, ext);
                        Z3_ast newresult = Z3_mk_concat(ctx, result, ext);
                        Z3_inc_ref(ctx, newresult);
                        Z3_dec_ref(ctx, ext);
                        Z3_dec_ref(ctx, result);
                        return newresult;
                    }
                    else {
                        nbytes -= fast;
                        Z3_ast newresult = Z3_mk_concat(ctx, result, m_ast[nbytes]);
                        Z3_inc_ref(ctx, newresult);
                        Z3_dec_ref(ctx, result);
                        result = newresult;
                    }
                }

            }
            else {
                auto zsort = Z3_mk_bv_sort(ctx, nbytes << 3);
                Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
                reast = Z3_mk_unsigned_int64(ctx, GET8(r_bytes), zsort);
                Z3_inc_ref(ctx, reast);
                Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
                Z3_ast newresult = Z3_mk_concat(ctx, result, reast);
                Z3_inc_ref(ctx, newresult);
                Z3_dec_ref(ctx, reast);
                Z3_dec_ref(ctx, result);
                return newresult;
            }
        }
        return result;
    }


#ifdef USE_HASH_AST_MANAGER
    Z3_ast TR::freg2Ast_cov(int nbytes, UChar * r_bytes, UChar * ast_fastindex, TR::AstManager::AstManagerX && m_ast, z3::vcontext & ctx, z3::vcontext & toctx) {
#else
    Z3_ast TR::freg2Ast_cov(int nbytes, UChar * r_bytes, UChar * ast_fastindex, Z3_ast * m_ast, z3::vcontext & ctx, z3::vcontext & toctx) {
#endif
        vassert(nbytes <= 8);
        ULong scan = GET8(ast_fastindex);
        Z3_ast result;
        Int index;
        Z3_ast reast;
        if (clzll(index, scan & fastMask(nbytes << 3))) {
            index = 63 - index;
            auto offset = (index >> 3);
            Char relen = nbytes - offset - 1;
            auto fast = ast_fastindex[offset];
            if (relen) {
                nbytes -= relen;
                auto zsort = Z3_mk_bv_sort(toctx, relen << 3);
                Z3_inc_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
                reast = Z3_mk_unsigned_int64(toctx, GET8(r_bytes + nbytes), zsort);
                Z3_inc_ref(toctx, reast);
                if (fast > nbytes) {
                    Z3_ast need_extract = Z3_mk_extract(toctx, (fast << 3) - 1, (fast - nbytes) << 3, Translate(ctx, toctx, m_ast[nbytes - fast]));
                    Z3_inc_ref(toctx, need_extract);
                    result = Z3_mk_concat(toctx, reast, need_extract);
                    Z3_inc_ref(toctx, result);
                    Z3_dec_ref(toctx, need_extract);
                    nbytes -= fast;
                }
                else {
                    nbytes -= fast;
                    result = Z3_mk_concat(toctx, reast, Translate(ctx, toctx, m_ast[nbytes]));
                    Z3_inc_ref(toctx, result);
                }
                Z3_dec_ref(toctx, reast);
                Z3_dec_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
            }
            else {
                if (nbytes < fast) {
                    result = Z3_mk_extract(toctx, ((fast) << 3) - 1, (fast - nbytes) << 3, Translate(ctx, toctx, m_ast[nbytes - fast]));
                    Z3_inc_ref(toctx, result);
                    return result;
                }
                if (ast_fastindex[nbytes] >> 1) {
                    result = Z3_mk_extract(toctx, (fast << 3) - 1, 0, Translate(ctx, toctx, m_ast[nbytes - fast]));
                    nbytes -= fast;
                }
                else {
                    if (nbytes == fast) {
                        Translate ret(ctx, toctx, m_ast[nbytes - fast]);
                        Z3_inc_ref(toctx, ret);
                        return ret;
                    }
                    else {
#if !defined(CLOSECNW)&&!defined(USECNWNOAST)
                        spin_unique_lock lock(ctx);
#endif
                        result = Z3_translate(ctx, m_ast[nbytes - fast], toctx);
                        nbytes -= fast;
                    }
                }
                Z3_inc_ref(toctx, result);
            }
        }
        else {
            auto zsort = Z3_mk_bv_sort(toctx, nbytes << 3);
            Z3_inc_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
            reast = Z3_mk_unsigned_int64(toctx, GET8(r_bytes), zsort);
            Z3_inc_ref(toctx, reast);
            Z3_dec_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
            return reast;
        }
        while (nbytes > 0) {
            if (clzll(index, scan & fastMask(nbytes << 3))) {
                index = 63 - index;
                auto offset = index >> 3;
                Char relen = nbytes - offset - 1;
                auto fast = ast_fastindex[offset];
                if (relen) {
                    nbytes -= relen;
                    auto zsort = Z3_mk_bv_sort(toctx, relen << 3);
                    Z3_inc_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
                    reast = Z3_mk_unsigned_int64(toctx, GET8(r_bytes + nbytes), zsort);
                    Z3_inc_ref(toctx, reast);
                    Z3_dec_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
                    Z3_ast newresult = Z3_mk_concat(toctx, result, reast);
                    Z3_inc_ref(toctx, newresult);
                    Z3_dec_ref(toctx, result);
                    Z3_dec_ref(toctx, reast);
                    if (nbytes < fast) {
                        Z3_ast ext = Z3_mk_extract(toctx, ((fast) << 3) - 1, (fast - nbytes) << 3, Translate(ctx, toctx, m_ast[nbytes - fast]));
                        Z3_inc_ref(toctx, ext);
                        Z3_ast result = Z3_mk_concat(toctx, newresult, ext);
                        Z3_inc_ref(toctx, result);
                        Z3_dec_ref(toctx, newresult);
                        Z3_dec_ref(toctx, ext);
                        return result;
                    }
                    else {
                        result = Z3_mk_concat(toctx, newresult, Translate(ctx, toctx, m_ast[nbytes - fast]));
                        Z3_inc_ref(toctx, result);
                        Z3_dec_ref(toctx, newresult);
                        nbytes -= fast;
                    }
                }
                else {
                    if (nbytes < fast) {
                        Z3_ast ext = Z3_mk_extract(toctx, ((fast) << 3) - 1, (fast - nbytes) << 3, Translate(ctx, toctx, m_ast[nbytes - fast]));
                        Z3_inc_ref(toctx, ext);
                        Z3_ast newresult = Z3_mk_concat(toctx, result, ext);
                        Z3_inc_ref(toctx, newresult);
                        Z3_dec_ref(toctx, ext);
                        Z3_dec_ref(toctx, result);
                        return newresult;
                    }
                    else {
                        nbytes -= fast;
                        Z3_ast newresult = Z3_mk_concat(toctx, result, Translate(ctx, toctx, m_ast[nbytes]));
                        Z3_inc_ref(toctx, newresult);
                        Z3_dec_ref(toctx, result);
                        result = newresult;
                    }
                }

            }
            else {
                auto zsort = Z3_mk_bv_sort(toctx, nbytes << 3);
                Z3_inc_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
                reast = Z3_mk_unsigned_int64(toctx, GET8(r_bytes), zsort);
                Z3_inc_ref(toctx, reast);
                Z3_dec_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
                Z3_ast newresult = Z3_mk_concat(toctx, result, reast);
                Z3_inc_ref(toctx, newresult);
                Z3_dec_ref(toctx, reast);
                Z3_dec_ref(toctx, result);
                return newresult;
            }
        }
        return result;
    }


    static inline Z3_ast mk_large_int(Z3_context ctx, void* data, UInt nbit) {
        return sv::symbol::_mk_ast(ctx, (uint64_t*)data, nbit);
    }

    //取值函数。将多个ast和真值组合为一个ast
#ifdef USE_HASH_AST_MANAGER
    Z3_ast TR::freg2AstSSE(int nbytes, UChar * r_bytes, UChar * ast_fastindex, AstManager::AstManagerX && m_ast, z3::vcontext & ctx) {
#else
    Z3_ast TR::freg2AstSSE(int nbytes, UChar * r_bytes, UChar * ast_fastindex, Z3_ast * m_ast, z3::vcontext & ctx) {
#endif
        vassert(nbytes <= 32);
        UInt scan = ~_mm256_movemask_epi8(_mm256_cmpeq_epi8(_mm256_setzero_si256(), _mm256_loadu_si256((__m256i*)ast_fastindex)));
        Z3_ast result;
        Int index;
        Z3_ast reast;
        if (clzll(index, scan & fastMask(nbytes))) {
            index = 63 - index;
            Char relen = nbytes - index - 1;
            auto fast = ast_fastindex[index];
            if (relen) {
                nbytes -= relen;
                reast = mk_large_int(ctx, r_bytes + nbytes, relen << 3);
                if (fast > nbytes) {
                    Z3_ast need_extract = Z3_mk_extract(ctx, (fast << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
                    Z3_inc_ref(ctx, need_extract);
                    result = Z3_mk_concat(ctx, reast, need_extract);
                    Z3_inc_ref(ctx, result);
                    Z3_dec_ref(ctx, need_extract);
                    nbytes -= fast;
                }
                else {
                    nbytes -= fast;
                    result = Z3_mk_concat(ctx, reast, m_ast[nbytes]);
                    Z3_inc_ref(ctx, result);
                }
                Z3_dec_ref(ctx, reast);
            }
            else {
                if (nbytes < fast) {
                    result = Z3_mk_extract(ctx, ((fast) << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
                    Z3_inc_ref(ctx, result);
                    return result;
                }
                if (ast_fastindex[nbytes] >> 1) {
                    result = Z3_mk_extract(ctx, (fast << 3) - 1, 0, m_ast[nbytes - fast]);
                    nbytes -= fast;
                }
                else {
                    if (nbytes == fast) {
                        Z3_inc_ref(ctx, m_ast[nbytes - fast]);
                        return m_ast[nbytes - fast];
                    }
                    else {
                        result = m_ast[nbytes - fast];
                        nbytes -= fast;
                    }
                }
                Z3_inc_ref(ctx, result);
            }
        }
        else {
            return mk_large_int(ctx, r_bytes, nbytes << 3);
        }
        while (nbytes > 0) {
            if (clzll(index, scan & fastMask(nbytes))) {
                index = 63 - index;
                Char relen = nbytes - index - 1;
                auto fast = ast_fastindex[index];
                if (relen) {
                    nbytes -= relen;
                    reast = mk_large_int(ctx, r_bytes + nbytes, relen << 3);
                    Z3_ast newresult = Z3_mk_concat(ctx, result, reast);
                    Z3_inc_ref(ctx, newresult);
                    Z3_dec_ref(ctx, result);
                    Z3_dec_ref(ctx, reast);
                    if (nbytes < fast) {
                        Z3_ast ext = Z3_mk_extract(ctx, ((fast) << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
                        Z3_inc_ref(ctx, ext);
                        Z3_ast result = Z3_mk_concat(ctx, newresult, ext);
                        Z3_inc_ref(ctx, result);
                        Z3_dec_ref(ctx, newresult);
                        Z3_dec_ref(ctx, ext);
                        return result;
                    }
                    else {
                        result = Z3_mk_concat(ctx, newresult, m_ast[nbytes - fast]);
                        Z3_inc_ref(ctx, result);
                        Z3_dec_ref(ctx, newresult);
                        nbytes -= fast;
                    }
                }
                else {
                    if (nbytes < fast) {
                        Z3_ast ext = Z3_mk_extract(ctx, ((fast) << 3) - 1, (fast - nbytes) << 3, m_ast[nbytes - fast]);
                        Z3_inc_ref(ctx, ext);
                        Z3_ast newresult = Z3_mk_concat(ctx, result, ext);
                        Z3_inc_ref(ctx, newresult);
                        Z3_dec_ref(ctx, ext);
                        Z3_dec_ref(ctx, result);
                        return newresult;
                    }
                    else {
                        nbytes -= fast;
                        Z3_ast newresult = Z3_mk_concat(ctx, result, m_ast[nbytes]);
                        Z3_inc_ref(ctx, newresult);
                        Z3_dec_ref(ctx, result);
                        result = newresult;
                    }
                }

            }
            else {
                reast = mk_large_int(ctx, r_bytes, nbytes << 3);
                Z3_ast newresult = Z3_mk_concat(ctx, result, reast);
                Z3_inc_ref(ctx, newresult);
                Z3_dec_ref(ctx, reast);
                Z3_dec_ref(ctx, result);
                return newresult;
            }
        }
        return result;
    }

#ifdef USE_HASH_AST_MANAGER
    Z3_ast TR::freg2AstSSE_cov(int nbytes, UChar * r_bytes, UChar * ast_fastindex, AstManager::AstManagerX && m_ast, z3::vcontext & ctx, z3::vcontext & toctx) {
#else
    Z3_ast TR::freg2AstSSE_cov(int nbytes, UChar * r_bytes, UChar * ast_fastindex, Z3_ast * m_ast, z3::vcontext & ctx, z3::vcontext & toctx) {
#endif
        vassert(nbytes <= 32);
        UInt scan = ~_mm256_movemask_epi8(_mm256_cmpeq_epi8(_mm256_setzero_si256(), _mm256_loadu_si256((__m256i*)ast_fastindex)));
        Z3_ast result;
        Int index;
        Z3_ast reast;

        if (clzll(index, scan & fastMask(nbytes))) {
            index = 63 - index;
            Char relen = nbytes - index - 1;
            auto fast = ast_fastindex[index];
            if (relen) {
                nbytes -= relen;
                reast = mk_large_int(toctx, r_bytes + nbytes, relen << 3);
                if (fast > nbytes) {
                    Z3_ast need_extract = Z3_mk_extract(toctx, (fast << 3) - 1, (fast - nbytes) << 3, Translate(ctx, toctx, m_ast[nbytes - fast]));
                    Z3_inc_ref(toctx, need_extract);
                    result = Z3_mk_concat(toctx, reast, need_extract);
                    Z3_inc_ref(toctx, result);
                    Z3_dec_ref(toctx, need_extract);
                    nbytes -= fast;
                }
                else {
                    nbytes -= fast;
                    result = Z3_mk_concat(toctx, reast, Translate(ctx, toctx, m_ast[nbytes]));
                    Z3_inc_ref(toctx, result);
                }
                Z3_dec_ref(toctx, reast);
            }
            else {
                if (nbytes < fast) {
                    result = Z3_mk_extract(toctx, ((fast) << 3) - 1, (fast - nbytes) << 3, Translate(ctx, toctx, m_ast[nbytes - fast]));
                    Z3_inc_ref(toctx, result);
                    return result;
                }
                if (ast_fastindex[nbytes] >> 1) {
                    result = Z3_mk_extract(toctx, (fast << 3) - 1, 0, Translate(ctx, toctx, m_ast[nbytes - fast]));
                    nbytes -= fast;
                }
                else {
                    if (nbytes == fast) {
                        Translate ret(ctx, toctx, m_ast[nbytes - fast]);
                        Z3_inc_ref(toctx, ret);
                        return ret;
                    }
                    else {
#if !defined(CLOSECNW)&&!defined(USECNWNOAST)
                        spin_unique_lock lock(ctx);
#endif
                        result = Z3_translate(ctx, m_ast[nbytes - fast], toctx);
                        nbytes -= fast;
                    }
                }
                Z3_inc_ref(toctx, result);
            }
        }
        else {
            return mk_large_int(toctx, r_bytes, nbytes << 3);
        }
        while (nbytes > 0) {
            if (clzll(index, scan & fastMask(nbytes))) {
                index = 63 - index;
                Char relen = nbytes - index - 1;
                auto fast = ast_fastindex[index];
                if (relen) {
                    nbytes -= relen;
                    reast = mk_large_int(toctx, r_bytes + nbytes, relen << 3);
                    Z3_ast newresult = Z3_mk_concat(toctx, result, reast);
                    Z3_inc_ref(toctx, newresult);
                    Z3_dec_ref(toctx, result);
                    Z3_dec_ref(toctx, reast);
                    if (nbytes < fast) {
                        Z3_ast ext = Z3_mk_extract(toctx, ((fast) << 3) - 1, (fast - nbytes) << 3, Translate(ctx, toctx, m_ast[nbytes - fast]));
                        Z3_inc_ref(toctx, ext);
                        Z3_ast result = Z3_mk_concat(toctx, newresult, ext);
                        Z3_inc_ref(toctx, result);
                        Z3_dec_ref(toctx, newresult);
                        Z3_dec_ref(toctx, ext);
                        return result;
                    }
                    else {
                        result = Z3_mk_concat(toctx, newresult, Translate(ctx, toctx, m_ast[nbytes - fast]));
                        Z3_inc_ref(toctx, result);
                        Z3_dec_ref(toctx, newresult);
                        nbytes -= fast;
                    }
                }
                else {
                    if (nbytes < fast) {
                        Z3_ast ext = Z3_mk_extract(toctx, ((fast) << 3) - 1, (fast - nbytes) << 3, Translate(ctx, toctx, m_ast[nbytes - fast]));
                        Z3_inc_ref(toctx, ext);
                        Z3_ast newresult = Z3_mk_concat(toctx, result, ext);
                        Z3_inc_ref(toctx, newresult);
                        Z3_dec_ref(toctx, ext);
                        Z3_dec_ref(toctx, result);
                        return newresult;
                    }
                    else {
                        nbytes -= fast;
                        Z3_ast newresult = Z3_mk_concat(toctx, result, Translate(ctx, toctx, m_ast[nbytes]));
                        Z3_inc_ref(toctx, newresult);
                        Z3_dec_ref(toctx, result);
                        result = newresult;
                    }
                }

            }
            else {
                reast = mk_large_int(toctx, r_bytes, nbytes << 3);
                Z3_ast newresult = Z3_mk_concat(toctx, result, reast);
                Z3_inc_ref(toctx, newresult);
                Z3_dec_ref(toctx, reast);
                Z3_dec_ref(toctx, result);
                return newresult;
            }
        }
        return result;
    }

    };
