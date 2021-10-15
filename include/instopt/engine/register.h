#pragma once
/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    Reister.class: 
Abstract:
    API list;
Author:
    WXC 2019-05-31.
Revision History:
--*/
#ifndef REGISTER_HL_CD
#define REGISTER_HL_CD

#include "instopt/engine/engine.h"
#include "instopt/engine/basic_var.hpp"


#define fastMaskB(n) fastMask(((n)<<3))
#define fastMaskBI1(n) fastMask((((n)+1)<<3))
class PAGE_DATA;

namespace TR { class Register; };
namespace re {
    //写入记录器，8字节记录为m_flag的一个bit
    
    class Record {
        int maxlength;
    public:
        UChar m_flag[0];
        Record(int maxlength) :maxlength(maxlength) {
            memset(m_flag, 0, sizeof((maxlength >> 6) + 1));
            UInt shift = (maxlength & ((1 << 6) - 1)) >> 3;
            m_flag[maxlength >> 6] = shift ? 0x1 << shift : 0x1;
        };

        void clearRecord() {
            memset(m_flag, 0, sizeof((maxlength >> 6) + 1));
            UInt shift = (maxlength & ((1 << 6) - 1)) >> 3;
            m_flag[maxlength >> 6] = shift ? 0x1 << shift : 0x1;
        };

        template<int nbytes>
        inline void write(int offset) {
            *(UShort*)(m_flag + (offset >> 6)) |=
                (UShort)
                (
                    (offset + nbytes) < ALIGN(offset, 8) + 8
                    ?
                    (nbytes <= 8) ? 0x01u :
                    (nbytes == 16) ? 0b11u :
                    0b1111u
                    :
                    (nbytes <= 8) ? 0b11u :
                    (nbytes == 16) ? 0b111u :
                    0b11111u
                    ) << ((offset >> 3) & 7);

        }

        template<> inline void write<1>(int offset) { m_flag[offset >> 6] |= 1 << ((offset >> 3) & 7); }



        inline UInt get_count() {
            UInt write_count = 0;
            for (auto offset : *this) {
                write_count += 1;
            }
            return write_count;
        }

        //写入遍历器
        class iterator
        {
        private:
            UInt _pcur;
            UInt m_len;
            ULong* m_flag;
        public:
            inline iterator(UChar* flag) :_pcur(0), m_len(0), m_flag((ULong*)flag){
                Int N;
                for (; ; _pcur += 64) {
                    if (ctzll(N, m_flag[_pcur >> 6])) {
                        _pcur += N;
                        return;
                    }
                }
            }
            iterator(UChar* flag, UInt length) :
                _pcur(length >> 3), m_len(length), m_flag((ULong *)flag)
            {}
            inline bool operator!=(const iterator& src)
            {
                return (_pcur << 3) < src.m_len;
            }

            inline void operator++()
            {
                int N;
                for (;;) {
                    if (ctzll(N, m_flag[_pcur >> 6] & fastMaskReverse(_pcur % 64))) {
                        _pcur = ALIGN(_pcur, 64) + N;
                        return;
                    }
                    else {
                        _pcur = ALIGN(_pcur + 64, 64);
                    }
                }
            }

            inline int operator*()
            {
                return (_pcur++) << 3;
            }
        };

        inline iterator begin() {
            return iterator(m_flag);
        }

        inline iterator end() {
            return iterator(m_flag, maxlength);
        }
    };


    //class reg_trace {
    //    TR::Register& m_reg;
    //public:
    //    reg_trace(TR::Register& reg) :m_reg(reg) { }
    //    virtual void write(UInt offset, UInt size) { }
    //    virtual void read(UInt offset, HWord ea, UInt size) { }
    //    virtual ~reg_trace() {}
    //};
};




namespace TR {

    class VRegs;
    class mem_unit;

    class AstManager {
        friend class AstManagerX;
        friend class Register;
    public:
        HASH_MAP<Int, Z3_ast> m_mem;
        class AstManagerX {
            HASH_MAP<Int, Z3_ast>& m_mem;
            Int m_offset;
        public:
            inline AstManagerX(AstManager& am) :m_mem(am.m_mem), m_offset(0) {}
            inline AstManagerX(AstManager& am, Int offset) : m_mem(am.m_mem), m_offset(offset) {}
            inline AstManagerX(HASH_MAP<Int, Z3_ast>& mem, Int offset) : m_mem(mem), m_offset(offset) {}
            inline Z3_ast& operator[](Int idx) { return m_mem[m_offset + idx]; }
            AstManagerX operator+(Int offset) { return AstManagerX(m_mem, m_offset + offset); }
            AstManagerX operator-(Int offset) { return AstManagerX(m_mem, m_offset - offset); }
        };
        inline AstManager() {}
        inline Z3_ast& operator[](Int idx) { return m_mem[idx]; }
        inline AstManagerX operator+(Int offset) { return AstManagerX(*this, offset); }
        inline AstManagerX operator-(Int offset) { return AstManagerX(*this, -offset); }
    };


    extern void setfast(void* /*fast_ptr*/, UInt /*__nbytes*/);

    extern Z3_ast freg2Ast(int nbytes, UChar* m_bytes, UChar* m_fastindex, TR::AstManager::AstManagerX&& m_ast, z3::vcontext& ctx);
    extern Z3_ast freg2AstSSE(int nbytes, UChar* m_bytes, UChar* m_fastindex, TR::AstManager::AstManagerX&& m_ast, z3::vcontext& ctx);

// ctx convert
    extern Z3_ast freg2Ast_cov(int nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX&& m_ast, z3::vcontext& ctx, z3::vcontext& toctx);
    extern Z3_ast freg2AstSSE_cov(int nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX&& m_ast, z3::vcontext& ctx, z3::vcontext& toctx);




#define sse_check_zero_X256(data)  (_mm256_movemask_epi8(_mm256_cmpeq_epi64(_mm256_setzero_si256(), _mm256_loadu_si256((__m256i*)(data)))) != -1)
#define sse_check_zero_X128(data)  (_mm_movemask_epi8(_mm_cmpeq_epi64(_mm_setzero_si128(), _mm_loadu_si128((__m128i*)(data)))) != -1)


    //Symbolic

    //class RegUnit {
    //private:
    //    struct _Mstruct {
    //        unsigned long long m_ast : 48;
    //        bool w : 1;
    //        bool r : 1;
    //        bool e : 1;
    //        bool hook : 1;
    //    } pack;
    //public:
    //    inline void operator =(Z3_ast _ast) {
    //        pack.m_ast = (unsigned long long)_ast;
    //    }
    //    inline operator Z3_ast() {
    //        return (Z3_ast)pack.m_ast;
    //    }
    //    inline bool ar() {
    //        return pack.r;
    //    }
    //    inline bool aw() {
    //        return pack.w;
    //    }
    //    inline bool ae() {
    //        return pack.e;
    //    }
    //};


    class Symbolic final
    {
        z3::vcontext& m_ctx;
        UInt m_size;
        AstManager m_ast;
        /* SETFAST macro Setfast overstepping the bounds is not thread-safe(heap), so +32 solves the hidden bug !*/
        __declspec(align(16)) unsigned char m_fastindex[32];
        Symbolic(z3::vcontext& ctx, UInt size);
        Symbolic(z3::vcontext& ctx, Symbolic* father);
        ~Symbolic();
    public:
        inline unsigned char* ast_idx_list() { return m_fastindex; }
        inline AstManager& ast_select() { return m_ast; }
        static Symbolic* mk_Symbolic(z3::vcontext& ctx, UInt size);
        static Symbolic* mk_Symbolic(z3::vcontext& ctx, Symbolic* father);
        static void del_Symbolic(Symbolic*);
    };


    __declspec(align(16))
    class Register /*final*/ {
        friend class StateBase;
        friend class VRegs;
        z3::vcontext& m_ctx;
        Symbolic* m_symbolic;
        UInt m_size;
        bool m_is_symbolic;
        
        __declspec(align(16))
        UChar m_bytes[0];

        //void set_trace() { reg_trace }
        //auto getRecord() { return m_trace; }

        Register(z3::vcontext& ctx, UInt size);

        //翻译转换父register
        Register(Register& father_regs, z3::vcontext& ctx);

        void mk_Symbolic();

        template<int n>
        inline bool fast_check(UInt offset);
        template<> inline bool fast_check<8>(UInt offset) { return *(int8_t*)(m_symbolic->ast_idx_list() + offset); };
        template<> inline bool fast_check<16>(UInt offset) { return *(int16_t*)(m_symbolic->ast_idx_list() + offset); };
        template<> inline bool fast_check<32>(UInt offset) { return *(int32_t*)(m_symbolic->ast_idx_list() + offset); };
        template<> inline bool fast_check<64>(UInt offset) { return *(int64_t*)(m_symbolic->ast_idx_list() + offset); };
        template<> inline bool fast_check<128>(UInt offset) { return sse_check_zero_X128(m_symbolic->ast_idx_list() + offset); };
        template<> inline bool fast_check<256>(UInt offset) { return sse_check_zero_X256(m_symbolic->ast_idx_list() + offset); };


        template<int n>
        inline void fast_set_zero(UInt offset);
        template<> inline void fast_set_zero<8>(UInt offset) { *(int8_t*)(m_symbolic->ast_idx_list() + offset) = 0; };
        template<> inline void fast_set_zero<16>(UInt offset) { *(int16_t*)(m_symbolic->ast_idx_list() + offset) = 0; };
        template<> inline void fast_set_zero<32>(UInt offset) { *(int32_t*)(m_symbolic->ast_idx_list() + offset) = 0; };
        template<> inline void fast_set_zero<64>(UInt offset) { *(int64_t*)(m_symbolic->ast_idx_list() + offset) = 0; };
        template<> inline void fast_set_zero<128>(UInt offset) { _mm_storeu_si128((__m128i*) & m_symbolic->ast_idx_list()[offset], _mm_setzero_si128()); };
        template<> inline void fast_set_zero<256>(UInt offset) { _mm256_storeu_si256((__m256i*) & m_symbolic->ast_idx_list()[offset], _mm256_setzero_si256()); };


        template<int n>
        inline void fast_set(UInt offset);
        template<> inline void fast_set<8>(UInt offset) { *(int8_t*)(m_symbolic->ast_idx_list() + offset) = 0x01; };
        template<> inline void fast_set<16>(UInt offset) { *(int16_t*)(m_symbolic->ast_idx_list() + offset) = 0x0201; };
        template<> inline void fast_set<32>(UInt offset) { *(int32_t*)(m_symbolic->ast_idx_list() + offset) = 0x04030201; };
        template<> inline void fast_set<64>(UInt offset) { *(int64_t*)(m_symbolic->ast_idx_list() + offset) = 0x0807060504030201; };
        template<> inline void fast_set<128>(UInt offset) { _mm_storeu_si128((__m128i*) & m_symbolic->ast_idx_list()[offset], _mm_set_epi64x(0x100f0e0d0c0b0a09, 0x0807060504030201)); };
        template<> inline void fast_set<256>(UInt offset) { _mm256_storeu_si256((__m256i*) & m_symbolic->ast_idx_list()[offset], _mm256_set_epi64x(0x201f1e1d1c1b1a19, 0x1817161514131211, 0x100f0e0d0c0b0a09, 0x0807060504030201)); };

        ~Register();
    public:
        static Register* mk_Register(z3::vcontext& ctx, UInt size);
        static Register* mk_Register(Register& father_regs, z3::vcontext& ctx);
        static void del_Register(Register*);

        void init_padding_v(Char v);

        template<int nbytes, TASSERT(nbytes <= 8)>
        inline Z3_ast freg2Ast(UInt offset) {
            return TR::freg2Ast((int)nbytes, &m_bytes[offset], &m_symbolic->ast_idx_list()[offset], m_symbolic->ast_select() + offset, m_ctx);
        }

        template<int nbytes, TASSERT(nbytes > 8)>
        inline Z3_ast freg2Ast(UInt offset) {
            return TR::freg2AstSSE((int)nbytes, &m_bytes[offset], &m_symbolic->ast_idx_list()[offset], m_symbolic->ast_select() + offset, m_ctx);
        }

        template<int nbytes, TASSERT(nbytes <= 8)>
        inline Z3_ast freg2Ast(UInt offset, z3::vcontext& toctx) {
            return TR::freg2Ast_cov((int)nbytes, &m_bytes[offset], &m_symbolic->ast_idx_list()[offset], m_symbolic->ast_select() + offset, m_ctx, toctx);
        }

        template<int nbytes, TASSERT(nbytes > 8)>
        inline Z3_ast freg2Ast(UInt offset, z3::vcontext& toctx) {
            return TR::freg2AstSSE_cov((int)nbytes, &m_bytes[offset], &m_symbolic->ast_idx_list()[offset], m_symbolic->ast_select() + offset, m_ctx, toctx);
        }

        //-------------------------------- get --------------------------------------

        template<bool sign, int nbits, sv::z3sk sk, TASSERT(sk == Z3_BV_SORT)>
        inline sv::rsval<sign, nbits, sk> get(UInt offset) {
            if (m_is_symbolic && fast_check<nbits>(offset)) {
                return sv::rsval<sign, nbits, Z3_BV_SORT>(m_ctx, freg2Ast< (nbits >> 3) >(offset), no_inc{});
            }
            else {
                return sv::rsval<sign, nbits, Z3_BV_SORT>(m_ctx, &m_bytes[offset]);
            }
        }

        template<bool sign, int nbits, sv::z3sk sk, TASSERT(sk == Z3_FLOATING_POINT_SORT)>
        inline sv::rsval<sign, nbits, sk> get(UInt offset) {
            if (m_is_symbolic && fast_check<nbits>(offset)) {
                return sv::symbolic<sign, nbits, Z3_BV_SORT>(m_ctx, freg2Ast< (nbits >> 3) >(offset), no_inc{}).tofpa();
            }
            else {
                return sv::rsval<sign, nbits, Z3_FLOATING_POINT_SORT>(m_ctx, &m_bytes[offset]);
            }
        }

        template<IRType ty, class _svc = sv::IRty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> get(UInt offset) { return get<_svc::is_signed, _svc::nbits, _svc::sk>(offset); }

        template<typename ty, TASSERT(std::is_arithmetic<ty>::value), class _svc = sv::sv_cty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> get(UInt offset) { return get<_svc::is_signed, _svc::nbits, _svc::sk>(offset); }



        //-------------------------------- translate get --------------------------------------

        template<bool sign, int nbits, sv::z3sk sk, TASSERT(sk == Z3_BV_SORT)>
        inline sv::rsval<sign, nbits, sk> get(UInt offset, z3::vcontext& ctx) {
            if (m_is_symbolic && fast_check<nbits>(offset)) {
                return sv::rsval<sign, nbits, Z3_BV_SORT>(ctx, freg2Ast< (nbits >> 3) >(offset, ctx), no_inc{});
            }
            else {
                return sv::rsval<sign, nbits, sk>(ctx, &m_bytes[offset]);
            }
        }

        template<bool sign, int nbits, sv::z3sk sk, TASSERT(sk == Z3_FLOATING_POINT_SORT)>
        inline sv::rsval<sign, nbits, sk> get(UInt offset, z3::vcontext& ctx) {
            if (m_is_symbolic && fast_check<nbits>(offset)) {
                return sv::symbolic<sign, nbits, Z3_BV_SORT>(ctx, freg2Ast< (nbits >> 3) >(offset, ctx), no_inc{}).tofpa();
            }
            else {
                return sv::rsval<sign, nbits, sk>(ctx, &m_bytes[offset]);
            }
        }

        template<typename ty, TASSERT(std::is_arithmetic<ty>::value), class _svc = sv::sv_cty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> get(UInt offset, z3::vcontext& ctx) { return get<_svc::is_signed, _svc::nbits, _svc::sk>(offset, ctx); }

        template<IRType ty, class _svc = sv::IRty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> get(UInt offset, z3::vcontext& ctx) { return get<_svc::is_signed, _svc::nbits, _svc::sk>(offset, ctx); }





        //---------------------------------------------- set numreal ---------------------------------------------------


        template<typename DataTy, TASSERT(std::is_arithmetic<DataTy>::value && !sv::is_sse<DataTy>::value)>
        void set(UInt offset, DataTy data) {
            if (m_is_symbolic && fast_check<(sizeof(data) << 3)>(offset)) {
                clear(offset, sizeof(DataTy));
                fast_set_zero<(sizeof(DataTy) << 3)>(offset);
            }
            *(DataTy*)(m_bytes + offset) = data;
        }


        //simd 128
        template<typename DataTy, TASSERT(sizeof(DataTy) == 16 && sv::is_sse<DataTy>::value)>
        void set(UInt offset, const DataTy& data) {
            if (m_is_symbolic && fast_check<128>(offset)) {
                clear(offset, 16);
                fast_set_zero<128>(offset);
            }
            _mm_storeu_si128((__m128i*)(m_bytes + offset), _mm_loadu_si128((__m128i*) & data));
        }

        //simd 256
        template<typename DataTy, TASSERT(sizeof(DataTy) == 32 && sv::is_sse<DataTy>::value)>
        void set(UInt offset, const DataTy& data) {
            if (m_is_symbolic && fast_check<256>(offset)) {
                clear(offset, 32);
                fast_set_zero<256>(offset);
            }
            _mm256_storeu_si256((__m256i*)(m_bytes + offset), _mm256_loadu_si256((__m256i*) & data));
        }

        template<bool sign, int nbits, TASSERT(nbits <= 64)>
        inline void set(UInt offset, const sv::ctype_val<sign, nbits, Z3_BV_SORT>& data) {
            set(offset, data.value());
        }

        //---------------------------------------------- set ast ---------------------------------------------------

        // only n_bit 8, 16, 32, 64 ,128 ,256
        template<int nbits>
        inline void set(UInt offset, Z3_ast _ast) {
            mk_Symbolic();
            if (fast_check<nbits>(offset)) {
                clear(offset, (nbits >> 3));
            }
            fast_set<nbits>(offset);
            m_symbolic->ast_select()[offset] = _ast;
            Z3_inc_ref(m_ctx, _ast);
        }
        
        template<bool sign, int nbits>
        inline void set(UInt offset, const sv::symbolic<sign, nbits, Z3_BV_SORT>& data) {
            set<nbits>(offset, (Z3_ast)data);
        }

        template<bool sign, int nbits>
        inline void set(UInt offset, const sv::rsval<sign, nbits, Z3_BV_SORT>& data) {
            if (data.real()) {
                set(offset, data.tor());
            }else{
                set(offset, data.tos());
            }
        }

        //---------------------------------------------- Iex_Get ---------------------------------------------------
        // IRType or nbit
        sv::tval Iex_Get(UInt offset, IRType ty);

        //---------------------------------------------- Iex_Get TRANSLATE ---------------------------------------------------
        //ty = (IRType)nbits or IRType
        sv::tval Iex_Get(UInt offset, IRType ty, z3::vcontext& ctx);

        //---------------------------------------------- Ist_Put ---------------------------------------------------
        void Ist_Put(UInt offset, sv::tval const& ir);
        //  slowly
        void Ist_Put(UInt offset, const void* data, UInt nbytes);
        // slowly
        void Ist_Put(UInt offset, Z3_ast _ast, UInt nbytes);
        //is slowly 
        sv::tval Iex_Get(UInt offset, UInt nbytes);
        //is slowly 变长取值
        sv::tval Iex_Get(UInt offset, UInt nbytes, z3::vcontext& ctx);
        //将fastindex offset位置的ast清空（剪切&释放）
        void clear(UInt org_offset, Int LEN);
        inline const UChar* get_bytes(UInt offset) const { return &m_bytes[offset]; }
        inline void write_regs(int offset, void* addr, int length) { memcpy(m_bytes + offset, addr, length); };
        inline void read_regs(int offset, void* addr, int length) { memcpy(addr, m_bytes + offset, length); };


    private:
        inline void Ist_Put(UInt, Z3_ast) = delete;
        inline void Ist_Put(UInt, Z3_ast&) = delete;
        inline void set(UInt, Z3_ast) = delete;
        inline void set(UInt, Z3_ast&) = delete;
        Register(const Register& father_regs) = delete;
        void operator = (Register& a) = delete;
    };

};



#endif //REGISTER_HL
