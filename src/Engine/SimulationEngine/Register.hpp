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
#define REGISTER_LEN 1000

#include "../engine.hpp"
#include "Variable.hpp"

extern __m256i m32_fast[33];
extern __m256i m32_mask_reverse[33];
extern Z3_ast Reg2Ast(Char nbytes, UChar* m_bytes, UChar* m_fastindex, Z3_ast* m_ast, Z3_context ctx);



#define SETFAST(fast_ptr,__nbytes)                                           \
if((__nbytes)<8){                                                            \
__asm__(                                                                     \
    "mov %[nbytes],%%cl;\n\t"                                                \
    "shl $3,%%rcx;\n\t"                                                      \
    "mov %[fast],%%rax;\n\t"                                                 \
    "shr %%cl,%%rax;\n\t"                                                    \
    "shl %%cl,%%rax;\n\t"                                                    \
    "mov $0x0807060504030201,%%rbx;\n\t"                                     \
    "sub $65,%%cl;\n\t"                                                      \
    "not %%cl;\n\t"                                                          \
    "shl %%cl,%%rbx;\n\t"                                                    \
    "shr %%cl,%%rbx;\n\t"                                                    \
    "or %%rbx,%%rax;\n\t"                                                    \
    "mov %%rax,%[out];\n\t"                                                  \
    : [out]"=r"(GET8((fast_ptr)))                                            \
    : [fast] "r"(GET8((fast_ptr))), [nbytes] "r"((UChar)(__nbytes))          \
    : "rax", "rbx", "rcx"                                                    \
);}                                                                          \
else if((__nbytes)<=16){                                                     \
    _mm_store_si128(                                                         \
        (__m128i*)(fast_ptr),                                                \
        _mm_or_si128(                                                        \
            _mm_and_si128(                                                   \
                GET16((fast_ptr)),                                           \
                GET16(&m32_mask_reverse[__nbytes])                           \
            ),                                                               \
            GET16(&m32_fast[__nbytes])                                       \
        )                                                                    \
    );                                                                       \
}else{                                                                       \
    _mm256_store_si256(                                                      \
        (__m256i*)(fast_ptr),                                                \
        _mm256_or_si256(                                                     \
            _mm256_and_si256(                                                \
                GET32((fast_ptr)),                                           \
                m32_mask_reverse[__nbytes]                                   \
            ),                                                               \
            m32_fast[__nbytes]                                               \
        )                                                                    \
    );                                                                       \
}



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

template<int maxlength>
class Symbolic
{
    template <int maxlength>
    friend class Register;
public:
    /* SETFAST macro Setfast overstepping the bounds is not thread-safe(heap), so +32 solves the hidden bug !*/
    __declspec(align(32)) UChar m_fastindex[maxlength + 32];
    __declspec(align(8)) Z3_ast m_ast[maxlength];
    Z3_context m_ctx;
    inline Symbolic(Z3_context ctx) : m_ctx(ctx) {
        memset(m_fastindex, 0, sizeof(m_fastindex));
    }
    inline Symbolic(Z3_context ctx, Symbolic<maxlength> *father) : m_ctx(ctx) {
        memcpy(m_fastindex, father->m_fastindex, maxlength);
        m_fastindex[maxlength] = 0;
        Int _pcur = maxlength - 1;
        DWORD N;
        for (; _pcur > 0; ) {
            if (_BitScanReverse64(&N, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1[_pcur % 8])) {
                _pcur = ALIGN(_pcur, 8) + (N >> 3);
                _pcur = _pcur - m_fastindex[_pcur] + 1;
                m_ast[_pcur] = Z3_translate(father->m_ctx, father->m_ast[_pcur], m_ctx);
                vassert(m_ast[_pcur] != NULL);
                Z3_inc_ref(m_ctx, m_ast[_pcur]);
                _pcur--;
            }
            else {
                _pcur = ALIGN(_pcur - 8, 8) + 7;
            }
        };

    }
    inline ~Symbolic<maxlength>() {
        int _pcur = maxlength - 1;
        DWORD N;
        for (; _pcur > 0; ) {
            if (_BitScanReverse64(&N, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1[_pcur % 8])) {
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
};


//Record

template<int maxlength>
class Record {
public:
    UChar m_flag[(maxlength >> 6) + 1];
    Record() {
        memset(m_flag, 0, sizeof(m_flag)); m_flag[maxlength >> 6] = 0x1;
    };

    template<int length>
    inline void write(int offset) {
        if (length == 1) {
            m_flag[offset >> 6] |= 1 << ((offset >> 3) % 8);
        }
        else {
            *(UShort*)(m_flag + (offset >> 6)) |=
                (UShort)
                (
                (offset + length) < ALIGN(offset, 8) + 8
                    ?
                    (maxlength <= 8) ? 0x01ull :
                    (maxlength == 16) ? 0b11ull :
                    0b1111ull
                    :
                    (maxlength <= 8) ? 0x11ull :
                    (maxlength == 16) ? 0b111ull :
                    0b11111ull
                    ) << ((offset >> 3) % 8);
        }
    }

    class iterator
    {
    private:
        int _pcur;
        ULong *m_flag;
    public:
        inline iterator(UChar *flag) :_pcur(0), m_flag((ULong*)flag) {
            DWORD N;
            for (; ; _pcur += 64) {
                if (_BitScanForward64(&N, m_flag[_pcur >> 6])) {
                    _pcur += N;
                    return;
                }
            }
        }
        iterator(UChar *flag, int length) :
            _pcur(length >> 3),
            m_flag((ULong*)flag)
        {}
        inline bool operator!=(const iterator &src)
        {
            return _pcur < src._pcur;
        }

        inline void operator++()
        {
            unsigned long N;
            for (;;) {
                if (_BitScanForward64(&N, m_flag[_pcur >> 6] & fastMaskReverse[_pcur % 64])) {
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



//Register<maxlength>




inline Z3_ast Reg2Ast(Char nbytes, UChar* m_bytes, UChar *m_fastindex, Z3_ast* m_ast, Z3_context ctx, Z3_context toctx) {
    auto res = Reg2Ast(nbytes, m_bytes, m_fastindex, m_ast, ctx);
    auto tast = Z3_translate(ctx, res, toctx);
    Z3_inc_ref(toctx, tast);
    Z3_dec_ref(ctx, res);
    return tast;
}


#define GET_from_nbytes(nbytes, ... )    \
((nbytes)==1)? \
    GET1(__VA_ARGS__): \
    ((nbytes)==2)? \
        GET2(__VA_ARGS__):\
        ((nbytes)==4)? \
            GET4(__VA_ARGS__):\
            ((nbytes)==8)? \
                GET8(__VA_ARGS__):\
                GET1(23333)//imPOSSIBLE
#define SET_from_nbytes(nbytes, arg1, arg2 )    \
((nbytes)==1)? \
    SET1( arg1, arg2): \
    ((nbytes)==2)? \
        SET2( arg1, arg2):\
        ((nbytes)==4)? \
            SET4( arg1, arg2):\
            ((nbytes)==8)? \
                SET8( arg1, arg2):\
                SET1(23333,0)//imPOSSIBLE

template<int maxlength>
class Register {
public:
    Z3_context m_ctx;
    __declspec(align(32)) UChar m_bytes[maxlength];
    Symbolic<maxlength> *symbolic;
    Record<maxlength> *record;

    inline Register(Z3_context ctx, Bool _need_record) :
        m_ctx(ctx),
        record(_need_record ? new Record<maxlength>() : NULL),
        symbolic(NULL)
    { }

    inline Register(Register<maxlength>& father_regs, Z3_context ctx, Bool _need_record) :
        m_ctx(ctx),
        record(_need_record ? new Record<maxlength>() : NULL),
        symbolic(father_regs.symbolic ? new Symbolic<maxlength>(m_ctx, father_regs.symbolic) : NULL)
    {
        memcpy(m_bytes, father_regs.m_bytes, maxlength);
    }

    ~Register<maxlength>() {
        if (symbolic) delete symbolic;
        if (record) delete record;
    };

#define m_fastindex symbolic->m_fastindex
#define m_ast symbolic->m_ast

    

    template<IRType ty>
    inline Vns Iex_Get(UInt offset) {
        switch (ty) {
#define lazydef(vectype,nbit,nbytes,compare)                                                                \
    case nbit:                                                                                              \
    case Ity_##vectype##nbit:                                                                               \
        if (symbolic&&compare) {                                                                            \
            return Vns(m_ctx, Reg2Ast(nbytes,m_bytes+offset,m_fastindex+offset, m_ast+offset, m_ctx), nbit,  no_inc {}); \
        }else{                                                                                              \
            return Vns(m_ctx, GET##nbytes##(m_bytes + offset));                                             \
        }

            lazydef(I, 8, 1, GET1(m_fastindex + offset));
            lazydef(I, 16, 2, GET2(m_fastindex + offset));
        case Ity_F32:
            lazydef(I, 32, 4, GET4(m_fastindex + offset));
        case Ity_F64:
            lazydef(I, 64, 8, GET8(m_fastindex + offset));
#undef lazydef
        case Ity_I128:
        case Ity_V128: {
            if (symbolic && ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)))) {
                auto ast_vector = Reg2Ast(8, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx);
                auto n_ast = Reg2Ast(8, m_bytes + offset + 8, m_fastindex + offset + 8, m_ast + offset + 8, m_ctx);
                auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
                Z3_inc_ref(m_ctx, new_vector);
                Z3_dec_ref(m_ctx, ast_vector);
                Z3_dec_ref(m_ctx, n_ast);
                return Vns(m_ctx, new_vector, 128, no_inc{});
            }
            else {
                return Vns(m_ctx, GET16(m_bytes + offset));
            }
        }
        case Ity_V256: {
            if (symbolic && ((GET8(m_fastindex + offset)) || (GET8(m_fastindex + offset + 8)) || (GET8(m_fastindex + offset + 16)) || (GET8(m_fastindex + offset + 24)))) {
                auto bytes_p = m_bytes + offset;
                auto fast_p = m_fastindex + offset;
                auto ast_p = m_ast + offset;
                auto ast_vector = Reg2Ast(8, bytes_p, fast_p, ast_p, m_ctx);
                for (int count = 8; count < 32; count += 8) {
                    auto n_ast = Reg2Ast(8, bytes_p + count, fast_p + count, ast_p + count, m_ctx);
                    auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
                    Z3_inc_ref(m_ctx, new_vector);
                    Z3_dec_ref(m_ctx, ast_vector);
                    Z3_dec_ref(m_ctx, n_ast);
                    ast_vector = new_vector;
                }
                return Vns(m_ctx, ast_vector, 256, no_inc{});
            }
            else {
                return Vns(m_ctx, GET32(m_bytes + offset));
            }
        }
        default: vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
        }
    }

    // IRType or nbit
    inline Vns Iex_Get(UInt offset, IRType ty) {
        switch (ty) {
#define lazydef(vectype,nbit)                                \
    case nbit:                                               \
    case Ity_##vectype##nbit:                                \
        return     Iex_Get<Ity_##vectype##nbit>(offset); 
            lazydef(I, 8);
            lazydef(I, 16);
        case Ity_F32:
            lazydef(I, 32);
        case Ity_F64:
            lazydef(I, 64);
        case Ity_V128:
            lazydef(I, 128);
            lazydef(V, 256);
#undef lazydef
        default: vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
        }
    }

    // <IRType> or <nbit>
    template<IRType ty>
    inline Vns Iex_Get(UInt offset, Z3_context ctx) {
        switch (ty) {
#define lazydef(vectype,nbit,nbytes,compare)                                                                            \
    case nbit:                                                                                                          \
    case Ity_##vectype##nbit:                                                                                           \
        if (symbolic&&compare) {                                                                                        \
            return Vns(ctx, Reg2Ast(nbytes, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx, ctx), nbit,  no_inc {});\
        }else{                                                                                                          \
            return Vns(ctx, GET##nbytes##(m_bytes + offset));                                                           \
        }                                                                            

            lazydef(I, 8, 1, GET1(m_fastindex + offset));
            lazydef(I, 16, 2, GET2(m_fastindex + offset));
        case Ity_F32:
            lazydef(I, 32, 4, GET4(m_fastindex + offset));
        case Ity_F64:
            lazydef(I, 64, 8, GET8(m_fastindex + offset));
#undef lazydef
        case Ity_I128:
        case Ity_V128: {
            auto fastindex = m_fastindex + offset;
            if (symbolic && ((GET8(fastindex)) || (GET8(fastindex + 8)))) {
                auto ast_vector = Reg2Ast(8, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx, ctx);
                auto n_ast = Reg2Ast(8, m_bytes + offset + 8, m_fastindex + offset + 8, m_ast + offset + 8, m_ctx, ctx);
                auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
                Z3_inc_ref(ctx, new_vector);
                Z3_dec_ref(ctx, n_ast);
                Z3_dec_ref(ctx, ast_vector);
                return Vns(ctx, new_vector, 128,  no_inc {});
            }
            else {
                return Vns(ctx, GET16(m_bytes + offset));
            }
        }
        case Ity_V256: {
            auto fastindex = m_fastindex + offset;
            if (symbolic && ((GET8(fastindex)) || (GET8(fastindex + 8)) || (GET8(fastindex + 16)) || (GET8(fastindex + 24)))) {
                auto bytes_p = m_bytes + offset;
                auto fast_p = m_fastindex + offset;
                auto ast_p = m_ast + offset;
                auto ast_vector = Reg2Ast(8, bytes_p, fast_p, ast_p, m_ctx, ctx);
                for (int count = 8; count < 32; count += 8) {
                    auto n_ast = Reg2Ast(8, bytes_p + count, fast_p + count, ast_p + count, m_ctx, ctx);
                    auto new_vector = Z3_mk_concat(ctx, n_ast, ast_vector);
                    Z3_inc_ref(ctx, new_vector);
                    Z3_dec_ref(ctx, ast_vector);
                    Z3_dec_ref(ctx, n_ast);
                    ast_vector = new_vector;
                }
                return Vns(ctx, ast_vector, 256, no_inc {});
            }
            else {
                return Vns(ctx, GET32(m_bytes + offset));
            }
        }
        default: vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
        }
    }

    //ty = (IRType)nbits or IRType
    inline Vns Iex_Get(UInt offset, IRType ty, Z3_context ctx) {
        switch (ty) {
#define lazydef(vectype,nbit)                                   \
    case nbit:                                                  \
    case Ity_##vectype##nbit:                                   \
        return     Iex_Get<Ity_##vectype##nbit>(offset, ctx);
            lazydef(I, 8);
            lazydef(I, 16);
        case Ity_F32:
            lazydef(I, 32);
        case Ity_F64:
            lazydef(I, 64);
        case Ity_V128:
            lazydef(I, 128);
            lazydef(V, 256);
#undef lazydef
        default: vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
        }
    }

    template<typename DataTy>
    inline void Ist_Put(UInt offset, DataTy data) {
        if (symbolic) {
            if (GET_from_nbytes(sizeof(DataTy), m_fastindex + offset))
            {
                clear(offset, sizeof(DataTy));
                SET_from_nbytes(sizeof(DataTy), m_fastindex + offset, 0);
            }
        }
        *(DataTy*)(m_bytes + offset) = data;
        if (record)  record->write<sizeof(DataTy)>(offset);
    }

#define B16_Ist_Put(DataTy)                                                                                     \
inline void Ist_Put(UInt offset, DataTy  data) {                                                                \
    if (symbolic) {                                                                                             \
        auto fastindex = m_fastindex + offset;                                                                  \
        if ((GET8(fastindex )) || (GET8(fastindex + 8)))                                                        \
        {                                                                                                       \
            clear(offset, 16);                                                                                  \
            *(__m128i*)(fastindex) = _mm_setzero_si128();                                                       \
        }                                                                                                       \
    }                                                                                                           \
    *(DataTy*)(m_bytes + offset) = data;                                                                        \
    if (record)  record->write<sizeof(DataTy)>(offset);                                                         \
}

#define B32_Ist_Put(DataTy)                                                                                     \
inline void Ist_Put(UInt offset, DataTy  data) {                                                                \
    if (symbolic) {                                                                                             \
        auto fastindex = m_fastindex + offset;                                                                  \
        if ((GET8(fastindex)) || (GET8(fastindex + 8)) || (GET8(fastindex + 16)) || (GET8(fastindex + 24)))     \
        {                                                                                                       \
            clear(offset, 32);                                                                                  \
            *(__m256i*)(fastindex) = _mm256_setzero_si256();                                                    \
        }                                                                                                       \
    }                                                                                                           \
    *(DataTy*)(m_bytes + offset) = data;                                                                        \
    if (record)  record->write<sizeof(DataTy)>(offset);                                                         \
}
    B16_Ist_Put(__m128i);
    B16_Ist_Put(__m128);
    B16_Ist_Put(__m128d);
    B32_Ist_Put(__m256i);
    B32_Ist_Put(__m256);
    B32_Ist_Put(__m256d);


    // only n_bit 8, 16, 32, 64 ,128 ,256
    template<unsigned int bitn>
    inline void Ist_Put(UInt offset, Z3_ast _ast) {
        if (!symbolic)
            symbolic = new Symbolic<maxlength>(m_ctx);
        if (bitn < 65) {
            if (GET_from_nbytes((bitn >> 3), m_fastindex + offset))
                clear(offset, (bitn >> 3));
        }
        else {
            auto fastindex = m_fastindex + offset;
            if (bitn == 128) {
                if ((GET8(fastindex)) || (GET8(fastindex + 8)))
                    clear(offset, 16);
            }
            else {
                if ((GET8(fastindex)) || (GET8(fastindex + 8)) || (GET8(fastindex + 16)) || (GET8(fastindex + 24)))
                    clear(offset, 32);
            }
        }
        if (bitn == 8)
            SET1(m_fastindex + offset, 0x01);
        else if (bitn == 16)
            SET2(m_fastindex + offset, 0x0201);
        else if (bitn == 32)
            SET4(m_fastindex + offset, 0x04030201);
        else if (bitn == 64)
            SET8(m_fastindex + offset, 0x0807060504030201);
        else if (bitn == 128){
            SET8(m_fastindex + offset, 0x0807060504030201);
            SET8(m_fastindex + offset + 8, 0x100f0e0d0c0b0a09);
        }
        else if (bitn == 256)
            SET32(m_fastindex + offset, _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19));
        else {
            vpanic("error len");
        }

        m_ast[offset] = _ast;
        Z3_inc_ref(m_ctx, _ast);
        if (record)
            record->write< (bitn >> 3) >(offset);
    }

    inline void Ist_Put(UInt offset, Vns const &ir) {
        if (ir.symbolic()) {
            switch (ir.bitn) {
            case 8: Ist_Put<8>(offset, (Z3_ast)ir); break;
            case 16:Ist_Put<16>(offset, (Z3_ast)ir); break;
            case 32:Ist_Put<32>(offset, (Z3_ast)ir); break;
            case 64:Ist_Put<64>(offset, (Z3_ast)ir); break;
            case 128:Ist_Put<128>(offset, (Z3_ast)ir); break;
            case 256:Ist_Put<256>(offset, (Z3_ast)ir); break;
            default:
                vpanic("error");
            }
        }
        else {
            switch (ir.bitn) {
            case 8: Ist_Put(offset, (UChar)ir); break;
            case 16:Ist_Put(offset, (UShort)ir); break;
            case 32:Ist_Put(offset, (UInt)ir); break;
            case 64:Ist_Put(offset, (ULong)ir); break;
            case 128:Ist_Put(offset, (__m128i)ir); break;
            case 256:Ist_Put(offset, (__m256i)ir); break;
            default:
                vpanic("error");
            }
        }
    }

    //  slowly
    void Ist_Put(UInt offset, void* data, UInt nbytes) {
        if (symbolic) { clear(offset, nbytes); memset(m_fastindex + offset, 0, nbytes); };
        memcpy(m_bytes + offset, data, nbytes);
        if (record) {
            auto _nbytes = nbytes;
            while (_nbytes) {
                if (_nbytes >= 8) { _nbytes -= 8; record->write<8>(offset + _nbytes); }
                else if (_nbytes >= 4) { _nbytes -= 4; record->write<4>(offset + _nbytes); }
                else if (_nbytes >= 2) { _nbytes -= 2; record->write<2>(offset + _nbytes); }
                else { _nbytes--; record->write<1>(offset + _nbytes); }
            }
        }
    }

    // slowly
    void Ist_Put(UInt offset, Z3_ast _ast, UInt nbytes) {
        if (!symbolic)
            symbolic = new Symbolic<maxlength>(m_ctx);
        clear(offset, nbytes);
        auto fastindex = m_fastindex + offset;
        for (int i = 0; i < nbytes; i++) { SET1(fastindex + i, i + 1); };
        m_ast[offset] = _ast;
        Z3_inc_ref(m_ctx, _ast);
        if (record) {
            auto _nbytes = nbytes;
            while (_nbytes) {
                if (_nbytes >= 8) { _nbytes -= 8; record->write<8>(offset + _nbytes); }
                else if (_nbytes >= 4) { _nbytes -= 4; record->write<4>(offset + _nbytes); }
                else if (_nbytes >= 2) { _nbytes -= 2; record->write<2>(offset + _nbytes); }
                else { _nbytes--; record->write<1>(offset + _nbytes); }
            }
        }
    }



    //is slowly 
    Vns Iex_Get(UInt offset, UInt nbytes) {
        if (this->symbolic) {
            auto fastindex = m_fastindex + offset;
            auto _nbytes = nbytes;
            while (_nbytes) {
                if (_nbytes >= 8) { _nbytes -= 8; if (GET8(fastindex + _nbytes)) { goto has_sym; }; }
                else if (_nbytes >= 4) { _nbytes -= 4; if (GET4(fastindex + _nbytes)) { goto has_sym; }; }
                else if (_nbytes >= 2) { _nbytes -= 2; if (GET2(fastindex + _nbytes)) { goto has_sym; }; }
                else { _nbytes--; if (GET1(fastindex + _nbytes)) { goto has_sym; }; }
            };

        }
        return Vns(m_ctx, GET32(m_bytes + offset), nbytes << 3);

    has_sym:
        auto bytes_p = m_bytes + offset;
        auto fast_p = m_fastindex + offset;
        auto ast_p = m_ast + offset;
        auto ast_vector = Reg2Ast(8, bytes_p, fast_p, ast_p, m_ctx);
        for (int count = 8; count < nbytes; count += 8) {
            auto n_ast = Reg2Ast(8, bytes_p + count, fast_p + count, ast_p + count, m_ctx);
            auto new_vector = Z3_mk_concat(m_ctx, n_ast, ast_vector);
            Z3_inc_ref(m_ctx, new_vector);
            Z3_dec_ref(m_ctx, ast_vector);
            Z3_dec_ref(m_ctx, n_ast);
            ast_vector = new_vector;
        }
        return Vns(m_ctx, ast_vector, nbytes << 3, no_inc{});
    }

    //is slowly 
    Vns Iex_Get(UInt offset, UInt nbytes, Z3_context ctx) {
        auto fastindex = m_fastindex + offset;
        auto _nbytes = nbytes;
        while (_nbytes) {
            if (_nbytes >= 8) { _nbytes -= 8; if (GET8(fastindex + _nbytes)) { goto has_sym; }; }
            else if (_nbytes >= 4) { _nbytes -= 4; if (GET4(fastindex + _nbytes)) { goto has_sym; }; }
            else if (_nbytes >= 2) { _nbytes -= 2; if (GET2(fastindex + _nbytes)) { goto has_sym; }; }
            else { _nbytes--; if (GET1(fastindex + _nbytes)) { goto has_sym; }; };
        }
        return Vns(ctx, GET32(m_bytes + offset), nbytes << 3);
    has_sym:
        auto bytes_p = m_bytes + offset;
        auto fast_p = m_fastindex + offset;
        auto ast_p = m_ast + offset;
        auto ast_vector = Reg2Ast(8, bytes_p, fast_p, ast_p, m_ctx, ctx);
        for (int count = 8; count < nbytes; count += 8) {
            auto n_ast = Reg2Ast(8, bytes_p + count, fast_p + count, ast_p + count, m_ctx, ctx);
            auto new_vector = Z3_mk_concat(ctx, n_ast, ast_vector);
            Z3_inc_ref(ctx, new_vector);
            Z3_dec_ref(ctx, ast_vector);
            Z3_dec_ref(ctx, n_ast);
            ast_vector = new_vector;
        }
        return Vns(ctx, ast_vector, nbytes << 3, no_inc{});
    }

    void clear(UInt org_offset, Int LEN)
    {
        Char length = LEN;
        char fastR = m_fastindex[org_offset + length] - 1;
        if (fastR > 0) {
            auto index = org_offset + length - fastR;
            auto sort_size = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast[index]));

            auto AstR = Z3_mk_extract(m_ctx, sort_size - 1, (fastR << 3), m_ast[index]);
            Z3_inc_ref(m_ctx, AstR);
            m_ast[org_offset + length] = AstR;
            SETFAST(m_fastindex + org_offset + length, (sort_size >> 3) - fastR);
            if (fastR > length) {
                register auto AstL = Z3_mk_extract(m_ctx, ((fastR - length) << 3) - 1, 0, m_ast[index]);
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
            register auto newAst = Z3_mk_extract(m_ctx, ((fastL) << 3) - 1, 0, m_ast[index]);
            Z3_inc_ref(m_ctx, newAst);
            Z3_dec_ref(m_ctx, m_ast[index]);
            m_ast[index] = newAst;
            org_offset += (sort_size - fastL);
            length -= (sort_size - fastL);
        }
        DWORD index;
        if (LEN <= 8) {
            ULong fast_index = GET8(m_fastindex + org_offset);
            while (length > 0) {
                if (_BitScanReverse64(&index, fast_index & fastMaskB[length])) {
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
                if (_BitScanReverse64(&index, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1[_pcur % 8])) {
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
    }

    inline void write_regs(int offset, void* addr, int length) {
        memcpy(m_bytes + offset, addr, length);
    }

    inline void read_regs(int offset, void* addr, int length) {
        memcpy(addr, m_bytes + offset, length);
    }


private:
    inline void Ist_Put(UInt, Z3_ast) = delete;
    inline void Ist_Put(UInt, Z3_ast&) = delete;
    Register(const Register<maxlength>& father_regs) = delete;
    void operator = (Register<maxlength>& a) = delete;
};


#ifndef UNDEFREG
#undef registercodedef
#undef GETASTSIZE
#undef SETFAST
#undef GET_from_nbytes
#undef SET_from_nbytes
#endif

#undef m_fastindex
#undef m_ast

#endif //REGISTER_HL
