#pragma once
/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    Variable.hpp:
Abstract:
    ·ûºÅ±äÁ¿
Author:
    WXC 2019-05-31.
Revision History:
--*/
#ifndef _Vns_H_
#define _Vns_H_

#include "valgrind/pub/libvex_basictypes.h"
#include "valgrind/pub/libvex_ir.h"
#include "z3++.h"
#include <mmintrin.h>  //MMX
#include <xmmintrin.h> //SSE(include mmintrin.h)
#include <emmintrin.h> //SSE2(include xmmintrin.h)
#include <pmmintrin.h> //SSE3(include emmintrin.h)
#include <tmmintrin.h> //SSSE3(include pmmintrin.h)
#include <smmintrin.h> //SSE4.1(include tmmintrin.h)
#include <nmmintrin.h> //SSE4.2(include smmintrin.h)
#include <wmmintrin.h> //AES(include nmmintrin.h)
#include <immintrin.h> //AVX(include wmmintrin.h)
#include <intrin.h>    //(include immintrin.h)
#include <Windows.h>


#define fastMask(n) ((ULong)((((int)(n))<64)?((1ull << ((int)(n))) - 1):-1ll))
#define fastMaskReverse(N) (~fastMask(N))

#if 0



static inline Z3_ast Z3_mk_neq(Z3_context ctx, Z3_ast a, Z3_ast b) { Z3_ast args[2] = { a, b }; return Z3_mk_distinct(ctx, 2, args); }

typedef enum :UChar {
    REAL = 0b00,
    REAL_BCKAST = 0b01,
    SYMB = 0b11,
}V_Kind;

struct no_inc {};

#define CP_DATA(a)                     \
if ((a).bitn <= 64) {                  \
    this->pack.i64 = (a).pack.i64;     \
}                                      \
else {                                 \
    this->pack.m128i = (a).pack.m128i; \
}                                      

#ifndef vassert
#define vassert(...) 
#endif // !vassert

#ifndef dassert
#define dassert(...) 
#endif // !dassert

#ifndef VPANIC
#define VPANIC(...) 
#endif // !VPANIC

class Vns {
public:
    __declspec(align(32)) union _pack {
        unsigned __int64    u64;
        unsigned __int32    u32;
        unsigned __int16    u16;
        unsigned __int8     u8;
        unsigned char		bit;
        double              d64;
        float               f32;
        __int8              i8;
        __int16             i16;
        __int32             i32;
        __int64             i64;
        __m64               m64;
        __m128              m128;
        __m128i             m128i;
        __m128d             m128d;
        __m256              m256;
        __m256i             m256i;
        __m256d             m256d;

        unsigned char		_bit[32];
        float               _f32[8];
        double              _d64[4];
        __int8              _i8[32];
        __int16             _i16[16];
        __int32             _i32[8];
        __int64             _i64[4];
        unsigned __int8     _u8[32];
        unsigned __int16    _u16[16];
        unsigned __int32    _u32[8];
        unsigned __int64    _u64[4];
        __m64               _m64[4];
        __m128              _m128[2];
        __m128i             _m128i[2];
        __m128d             _m128d[2];
    }pack;
    Z3_context m_ctx;
    Z3_ast m_ast;
    V_Kind m_kind;
    UShort bitn;

    inline Vns() : m_kind(REAL) {};//G
    template<typename T>
    inline Vns(Z3_context ctx, T v) :
        m_ctx(ctx),
        m_kind(REAL),
        bitn(sizeof(T) << 3)
    {
        *(T*)&this->pack = v;
    };

    template<typename T>
    inline Vns(z3::context const &ctx, T v) : Vns((Z3_context)ctx, v) {};

    template<typename T>
    explicit inline Vns(T v)  : Vns((Z3_context)0, v) {};

    template<typename T>
    inline Vns(Z3_context ctx, T v, UShort size) :
        m_ctx(ctx),
        m_kind(REAL),
        bitn(size)
    {
        *(T*)&this->pack = v;
    };

    template<typename T>
    inline Vns(z3::context const &ctx, T v, UShort size) : 
        Vns((Z3_context)ctx, v, size) {};

    inline Vns(Z3_context ctx, Z3_ast ast) :
        m_ctx(ctx),
        m_ast(ast),
        m_kind(SYMB)
    {
        Z3_inc_ref(ctx, ast);
#ifdef _DEBUG
        vassert(ast);
        vassert(Z3_OK == Z3_get_error_code(ctx));
#endif
        bitn = Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, m_ast));
    }

    inline Vns(Z3_context ctx, Z3_ast ast, no_inc) :
        m_ctx(ctx),
        m_ast(ast),
        m_kind(SYMB)
    {
        dassert(ast);
        dassert(Z3_OK == Z3_get_error_code(ctx));
        bitn = Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, m_ast));
    }

    inline Vns(z3::context const &ctx, Z3_ast ast) :
        Vns((Z3_context) ctx,  ast) {};

    inline Vns(z3::context const &ctx, Z3_ast ast, no_inc no) :
        Vns((Z3_context)ctx, ast, no) {};

    inline Vns(Z3_context ctx, Z3_ast ast, UShort n) ://main
        m_ctx(ctx),
        m_ast(ast),
        m_kind(SYMB),
        bitn(n)
    {
        Z3_inc_ref(ctx, ast);
#ifdef _DEBUG
        if (Z3_OK != Z3_get_error_code(ctx)) {
            VPANIC(Z3_get_error_msg(ctx, Z3_get_error_code(ctx)));
        }
        vassert(ast);
        if (sort_kind() == Z3_BV_SORT) {
            vassert(Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, m_ast)) == n);
        }
#endif
    }

    inline Vns(Z3_context ctx, Z3_ast ast, UShort n, no_inc) ://main
        m_ctx(ctx),
        m_ast(ast),
        m_kind(SYMB),
        bitn(n)
    {
#ifdef _DEBUG
        if (Z3_OK != Z3_get_error_code(ctx)) {
            VPANIC(Z3_get_error_msg(ctx, Z3_get_error_code(ctx)));
        }
        vassert(ast);
        if (sort_kind() == Z3_BV_SORT) {
            vassert(Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, m_ast)) == n);
        }
#endif
    }
    

    inline Vns(z3::context const &ctx, Z3_ast ast, UShort n) : 
        Vns((Z3_context)ctx,  ast,  n) {};

    inline Vns(z3::context const &ctx, Z3_ast ast, UShort n, no_inc  no) : 
        Vns((Z3_context)ctx, ast, n, no) {};

    inline Vns(z3::expr const &exp, UShort n) : 
        Vns(exp.ctx(), (Z3_ast)exp, n) {};

    inline Vns(Z3_context ctx, IRConst const *con) :
        m_ctx(ctx),
        m_kind(REAL)
    {
        switch (con->tag) {
        case Ico_U1:   bitn = 1;  this->pack.bit = con->Ico.U1; break;
        case Ico_U8:   bitn = 8;  this->pack.u8 = con->Ico.U8; break;
        case Ico_U16:  bitn = 16; this->pack.u16 = con->Ico.U16; break;
        case Ico_U32:  bitn = 32; this->pack.u32 = con->Ico.U32; break;
        case Ico_U64:  bitn = 64; this->pack.u64 = con->Ico.U64; break;
        case Ico_F32:  bitn = 32; this->pack.u32 = con->Ico.U32; break;
        case Ico_F32i: bitn = 32; this->pack.u32 = con->Ico.U32; break;
        case Ico_F64:  bitn = 64; this->pack.u64 = con->Ico.U64; break;
        case Ico_F64i: bitn = 64; this->pack.u16 = con->Ico.U64; break;
        case Ico_V128: bitn = 128; this->pack.m128i = _mm_set1_epi16(con->Ico.V128); break;
        case Ico_V256: bitn = 256; this->pack.m256i = _mm256_set1_epi32(con->Ico.V256); break;
        default: VPANIC("tIRConst");
        }
    }

    inline operator IRConstTag() const
    {
        switch (bitn) {
        case 1:  return Ico_U1;
        case 8:  return Ico_U8;
        case 16: return Ico_U16;
        case 32: return Ico_U32;
        case 64: return Ico_U64;
        case 128:return Ico_V128;
        case 256:return Ico_V256;
        default: 
            return (IRConstTag)bitn;
        }
    }
    inline Vns(z3::context const &ctx, IRConst const *con) :
        Vns((Z3_context)ctx, con) {};


    inline Vns(z3::context const& ctx, IRConst* con) :
        Vns((Z3_context)ctx, (IRConst const*)con) {};

    inline Vns(Z3_context ctx, bool tf) :
        Vns(ctx, tf, 1) {};

    inline Vns(z3::context const &ctx, bool tf) :
        Vns((Z3_context)ctx, tf, 1) {};


    template<typename T>
    inline void operator = (const T &a)
    {
        Vns::~Vns();
        *(T*)&this->pack = a;
        bitn = sizeof(a) << 3;
        m_kind = REAL;
    }

    inline Vns(const Vns &a) :
        m_ctx(a.m_ctx)
    {
        if (a.m_kind == REAL) {
            CP_DATA(a);
        }
        else {
            m_ast = a.m_ast;
            Z3_inc_ref(m_ctx, m_ast);
            if (a.m_kind == REAL_BCKAST) {
                CP_DATA(a);
            }
        }
        bitn = a.bitn;
        m_kind = a.m_kind;
    }

    inline void operator=(const Vns & a)
    {
        this->~Vns();
        this->Vns::Vns(a);
    }

    inline Vns(z3::expr &a) :
        m_ctx(a.ctx())
    {
        switch (Z3_get_sort_kind(m_ctx, Z3_get_sort(m_ctx, a))) {
        case	Z3_BOOL_SORT:
            bitn = 1;
            m_ast = a;
            Z3_inc_ref(m_ctx, m_ast);
            break;
        case	Z3_BV_SORT:
            m_ast = a;
            bitn = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast));
            Z3_inc_ref(m_ctx, m_ast);
            break;
        case	Z3_FLOATING_POINT_SORT:
            m_ast = Z3_mk_fpa_to_ieee_bv(m_ctx, m_ast);
            Z3_inc_ref(m_ctx, m_ast);
            bitn = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast));
            break;
        default: VPANIC("un know");
        }
        m_kind = SYMB;
    }

    inline void operator=(const z3::expr &a)
    {
        Vns::~Vns();
        m_ctx = a.ctx();
        switch (sort_kind()) {
        case	Z3_BOOL_SORT:
            bitn = 1;
            m_ast = a;
            Z3_inc_ref(m_ctx, m_ast);
            break;
        case	Z3_BV_SORT:
            m_ast = a;
            bitn = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast));
            Z3_inc_ref(m_ctx, m_ast);
            break;
        case	Z3_FLOATING_POINT_SORT:
            m_ast = Z3_mk_fpa_to_ieee_bv(m_ctx, m_ast);
            Z3_inc_ref(m_ctx, m_ast);
            bitn = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast));
            break;
        default: VPANIC("un know");
        }
        m_kind = SYMB;
    }

    template<typename T>
    inline operator T() const {
        dassert(real());
        return *(T*)(&this->pack);
    }

    inline operator Z3_context() const { return m_ctx; }

    operator Z3_ast() const {
        if (m_kind == REAL) {
            Z3_sort zsort = Z3_mk_bv_sort(m_ctx, (bitn > 64) ? 64 : bitn);
            Z3_inc_ref(m_ctx, reinterpret_cast<Z3_ast>(zsort));
            Z3_ast r_ast = Z3_mk_unsigned_int64(m_ctx, *this, zsort);
            Z3_inc_ref(m_ctx, r_ast);
            Z3_dec_ref(m_ctx, reinterpret_cast<Z3_ast>(zsort));
            if (bitn > 64) {
                for (int con = 1; con <= ((bitn-1) >> 6); con++) {
                    auto n = (bitn - (con << 6));
                    zsort = Z3_mk_bv_sort(m_ctx, (n < 64) ? n : 64);
                    Z3_inc_ref(m_ctx, reinterpret_cast<Z3_ast>(zsort));
                    auto new_ast = Z3_mk_unsigned_int64(m_ctx, this->pack._i64[con], zsort);
                    Z3_inc_ref(m_ctx, new_ast);
                    Z3_dec_ref(m_ctx, reinterpret_cast<Z3_ast>(zsort));
                    auto concat_ast = Z3_mk_concat(m_ctx, new_ast, r_ast);
                    Z3_inc_ref(m_ctx, concat_ast);
                    Z3_dec_ref(m_ctx, new_ast);
                    Z3_dec_ref(m_ctx, r_ast);
                    r_ast = concat_ast;
                }
            }
            //ÈÆ¹ýconst
            const_cast<Vns*>(this)->m_ast = r_ast;
            const_cast<Vns*>(this)->m_kind = REAL_BCKAST;
        };
        return m_ast;
    }

    inline operator Z3_sort() const { vassert(m_kind != REAL); return Z3_get_sort(m_ctx, *this); }

    operator std::string() const {
        std::string str;
        char buff[200];
        if (real()) {
            switch (bitn) {
            case 1:   snprintf(buff, sizeof(buff), " BV%d( %02x )", bitn, this->pack.bit); break;
            case 8:   snprintf(buff, sizeof(buff), " BV%d( %02x )", bitn, this->pack.u8); break;
            case 16:  snprintf(buff, sizeof(buff), " BV%d( %04x )", bitn, this->pack.u16); break;
            case 32:  snprintf(buff, sizeof(buff), " BV%d( %08x )", bitn, this->pack.u32); break;
            case 64:  snprintf(buff, sizeof(buff), " BV%d( %016llx )", bitn, this->pack.u64); break;
            case 128: snprintf(buff, sizeof(buff), " BV%d( %016llx %016llx )", bitn, this->pack.m128.m128_u64[1], this->pack.m128.m128_u64[0]); break;
            case 256: snprintf(buff, sizeof(buff), " BV%d( %016llx %016llx %016llx %016llx )", bitn, this->pack.m256i.m256i_u64[3], this->pack.m256i.m256i_u64[2], this->pack.m256i.m256i_u64[1], this->pack.m256i.m256i_u64[0]); break;
            default:  snprintf(buff, sizeof(buff), " BV%d( %016llx %016llx %016llx %016llx )", bitn, this->pack.m256i.m256i_u64[3], this->pack.m256i.m256i_u64[2], this->pack.m256i.m256i_u64[1], this->pack.m256i.m256i_u64[0]); break;
            }
            str.assign(buff);
        }
        else {
#if 0
            std::string strContent;
            snprintf(buff, sizeof(buff), " BS%d < ", bitn);
            strContent.assign(buff);
            str.append(strContent);
            strContent.assign(Z3_ast_to_string(m_ctx, m_ast));
            str.append(strContent);
            strContent.assign(" >");
            str.append(strContent);
#else
            snprintf(buff, sizeof(buff), " BVS %d < \\%p/ >  ", bitn, m_ast);
            str.assign(buff);
#endif
        }
        return str;
    }

    template<typename T, UChar offset>
    inline T get() const { assert(real()); return *(T*)(((UChar*)&this->pack) + offset); }

    inline Z3_ast ast(Z3_context ctx) const {
        return (ctx == m_ctx) ? *this : Z3_translate(m_ctx, *this, ctx);
    }

    inline bool real() const { return m_kind != SYMB; }

    inline bool symbolic() const { return  m_kind == SYMB; }

    inline Z3_sort_kind sort_kind() const { return Z3_get_sort_kind(m_ctx, Z3_get_sort(m_ctx, *this)); }

    inline Z3_ast_kind ast_kind() const { return Z3_get_ast_kind(m_ctx, *this); }

    inline Vns simplify() const
    {
        if (m_kind != SYMB)
            return *this;
        Z3_ast simp = Z3_simplify(m_ctx, m_ast);
        Z3_inc_ref(m_ctx, simp);
        if (sort_kind() == Z3_BV_SORT) {
            if (Z3_get_ast_kind(m_ctx, simp) == Z3_NUMERAL_AST) {
                if (bitn <= 64) {
                    uint64_t TMP;
                    Z3_get_numeral_uint64(m_ctx, simp, &TMP);
                    Z3_dec_ref(m_ctx, simp);
                    return Vns(m_ctx, TMP, bitn);
                }
                else {
                    __m256i buff;
                    Z3_get_numeral_bytes(m_ctx, simp, (ULong*)&buff);
                    Z3_dec_ref(m_ctx, simp);
                    return Vns(m_ctx, buff, bitn);
                }
            }
        }
        return Vns(m_ctx, simp, bitn, no_inc{});
    }

    inline Vns bv2fpa(z3::sort &s) const {
        return Vns(m_ctx, Z3_mk_fpa_to_fp_bv(m_ctx, *this, s), bitn);
    };

    inline Vns fpa2bv() const {
        return Vns(m_ctx, Z3_mk_fpa_to_ieee_bv(m_ctx, *this), bitn);
    };

    inline Vns integer2fp_bv(z3::sort &rm, z3::sort &fpa_sort) const {
        return Vns(m_ctx, Z3_mk_fpa_to_fp_signed(m_ctx, rm, *this, fpa_sort), bitn).fpa2bv();
    };
    inline Vns uinteger2fp_bv(z3::sort &rm, z3::sort &fpa_sort) const {
        return Vns(m_ctx, Z3_mk_fpa_to_fp_unsigned(m_ctx, rm, *this, fpa_sort), bitn).fpa2bv();
    };

    inline Vns fp2integer_bv(z3::sort &rm, z3::sort &fpa_sort) const {
        return Vns(m_ctx, Z3_mk_fpa_to_sbv(m_ctx, rm, bv2fpa(fpa_sort), bitn));
    };
    inline Vns fp2uinteger_bv(z3::sort &rm, z3::sort &fpa_sort) const {
        return Vns(m_ctx, Z3_mk_fpa_to_ubv(m_ctx, rm, bv2fpa(fpa_sort), bitn));
    };

    inline Vns fp2fp_bv(z3::sort &rm, z3::sort &fpa_sort, z3::sort &to_fpa_sort, UInt to_size) const {
        return Vns(m_ctx, Z3_mk_fpa_to_fp_float(m_ctx, rm, bv2fpa(fpa_sort), to_fpa_sort), to_size).fpa2bv().simplify();
    };

    /* bitn  */
    inline Vns Split(UChar size, UInt low) {
        if (m_kind == SYMB) {
            return Vns(m_ctx, Z3_mk_extract(m_ctx, low + size - 1, low, m_ast), size);
        }
        else {
            return extract(low + size - 1, low);
        }
    }

    template<unsigned int hi, unsigned int lo>
    inline Vns extract() const {
        if (m_kind == SYMB) {
            return Vns(m_ctx, Z3_mk_extract(m_ctx, hi, lo, m_ast), (hi - lo + 1));
        }
        else {
            if (lo < 64 && hi < 64) {
                return Vns(m_ctx, (ULong)(*this) >> lo, (hi - lo + 1));
            }
            __m256i m32 = GET32(&this->pack._i8[lo >> 3]);
            if (lo & 7) {
                UChar _n = (hi - lo + 1) >> 6;
                UChar _s = (64 - (lo & 7));
                for (int i = 0; i <= _n; i++) {
                    m32.m256i_u64[i] = (m32.m256i_u64[i] >> (lo & 7)) | (m32.m256i_u64[i + 1] << _s);
                }
            }
            if (m_kind == REAL) {
                return Vns(m_ctx, m32, (hi - lo + 1));
            }
            else {
                return Vns(m_ctx, m32, (hi - lo + 1));
            }
        }
    }

    Vns extract(UInt hi, UInt lo) const {
        UShort size = hi - lo + 1;
        if (m_kind == SYMB) {
            return Vns(m_ctx, Z3_mk_extract(m_ctx, hi, lo, m_ast), size);
        }
        else {
            if (lo < 64 && hi < 64) {
                return Vns(m_ctx, (ULong)(*this) >> lo, (hi - lo + 1));
            }
            __m256i m32 = *(__m256i*)(&this->pack._i8[lo >> 3]);
            if (lo & 7) {
                UChar _n = size >> 6;
                UChar _s = (64 - (lo & 7));
                for (int i = 0; i <= _n; i++) {
                    m32.m256i_u64[i] = (m32.m256i_u64[i] >> (lo & 7)) | (m32.m256i_u64[i + 1] << _s);
                }
            }
            if (m_kind == REAL) {
                return Vns(m_ctx, m32, size);
            }
            else {
                return Vns(m_ctx, m32, size);
            }
        }
    }


    Vns Concat(Vns const& low) const {
        vassert((low.bitn + bitn) <= 256);
        if (!low.bitn) return *this;
        if (!bitn) return low;
        if (real() && low.real()) {
            if (low.bitn & 7) {
                __m256i m32 = low;
                auto base = ((low.bitn - 1) >> 6);
                m32.m256i_u64[base] &= fastMask(low.bitn & 63);
                auto shln = low.bitn & 63;
                auto shrn = (64 - shln);
                m32.m256i_u64[base] |= this->pack.m256i.m256i_u64[0] << shln;
                for (int i = 1; i <= ((bitn-1) >> 6); i++) {
                    m32.m256i_u64[base + i] = (this->pack.m256i.m256i_u64[i] << shln) | (this->pack.m256i.m256i_u64[i - 1] >> shrn);
                }
                return Vns(m_ctx, m32, low.bitn + bitn);
            }
            else {
                __m256i re = low;
                memcpy(&re.m256i_u8[(low.bitn >> 3)], &this->pack, (this->bitn) >> 3);
                return Vns(m_ctx, re, low.bitn + bitn);
            }
        }
        else {
            return Vns(m_ctx, Z3_mk_concat(m_ctx, *this, low), low.bitn + bitn);
        }
    }


    Vns shl(UInt shn) const {
        vassert(shn < 256);
        if (real()) {
            if (bitn > 64) {
                if (shn & 7) {
                    __m256i m32 = _mm256_set1_epi64x(0ull);
                    auto base = (((UInt)shn - 1) >> 6);
                    m32.m256i_u64[base] &= fastMask((UInt)shn & 63);
                    auto shln = (UInt)shn & 63;
                    auto shrn = (64 - shln);
                    m32.m256i_u64[base] |= this->pack.m256i.m256i_u64[0] << shln;
                    for (int i = 1; i <= ((bitn - 1) >> 6); i++) {
                        m32.m256i_u64[base + i] = (this->pack.m256i.m256i_u64[i] << shln) | (this->pack.m256i.m256i_u64[i - 1] >> shrn);
                    }
                    return Vns(m_ctx, m32, bitn);
                }
                else {
                    __m256i re = _mm256_set1_epi64x(0ull);;
                    memcpy(&re.m256i_u8[((UInt)shn >> 3)], &this->pack, (this->bitn) >> 3);
                    return Vns(m_ctx, re,  bitn);
                }
            }
            else {
                return Vns(m_ctx, (ULong)(*this) << (UInt)shn, bitn);
            }
        }
        else {
            return Vns(m_ctx, Z3_mk_bvshl(m_ctx, *this, Vns(m_ctx, shn, bitn)),  bitn);
        }
    }

    Vns lshr(UInt shn) const {
        vassert(shn < 256);
        if (real()) {
            if (bitn > 64) {
                return extract(bitn-1, shn).zext(shn);
            }
            else {
                return Vns(m_ctx, ((ULong)(*this)& fastMask(bitn)) >> (UInt)shn, bitn);
            }
        }
        else {
            return Vns(m_ctx, Z3_mk_bvlshr(m_ctx, *this, Vns(m_ctx, shn, bitn)), bitn);
        }
    }

    Vns ashr(UInt shn) const {
        vassert(shn < 256);
        if (real()) {
            return extract(bitn - 1, shn).sext(shn);
        }
        else {
            return Vns(m_ctx, Z3_mk_bvashr(m_ctx, *this, Vns(m_ctx, shn, bitn)), bitn);
        }
    }

    inline Vns zext(int i) const {

        if (i < 0)
            return extract(bitn + i - 1, 0);
        if (m_kind == SYMB) {
            return Vns(m_ctx, Z3_mk_zero_ext(m_ctx, i, m_ast), bitn + i);
        }
        auto m32 = *(__m256i*)(&this->pack);
        if (bitn & 7) {
            m32.m256i_i8[(bitn - 1) >> 3] &= fastMask(bitn & 7);
        }
        memset(&m32.m256i_i8[((bitn - 1) >> 3) + 1], 0ul, i >> 3);
        if (m_kind == REAL) {
            return Vns(m_ctx, m32, bitn + i);
        }
        else {
            return Vns(m_ctx, m32, bitn + i);
        }
    }

    inline Vns sext(int i)const {
        if (i < 0)
            return extract(bitn + i - 1, 0);
        if (m_kind == SYMB) {
            return Vns(m_ctx, Z3_mk_sign_ext(m_ctx, i, m_ast), bitn + i);
        }
        auto m32 = *(__m256i*)(&this->pack);
        if ((this->pack._u8[(bitn - 1) >> 3] >> ((bitn-1) & 7)) & 1) {
            if (bitn & 7) {
                m32.m256i_i8[(bitn - 1) >> 3] |= fastMaskReverse((bitn & 7));
            }
            memset(&m32.m256i_i8[((bitn - 1) >> 3) + 1], -1ul, i >> 3);
        }
        else {
            if (bitn & 7) {
                m32.m256i_i8[(bitn - 1) >> 3] &= fastMask(8 - (bitn & 7));
            }
            memset(&m32.m256i_i8[((bitn - 1) >> 3) + 1], 0ul, i >> 3);
        }
        return Vns(m_ctx, m32, bitn + i);
    }

    inline Vns toZ3Bool() const
    {
        vassert(bitn == 1);
        if (m_kind == REAL) {
            if ((UChar)(*this))
                return Vns(m_ctx, Z3_mk_true(m_ctx), 1);
            else
                return Vns(m_ctx, Z3_mk_false(m_ctx), 1);
        }
        if (sort_kind() == Z3_BOOL_SORT) {
            return *this;
        }
        else {
            return Vns(m_ctx, Z3_mk_eq(m_ctx, *this, Vns(m_ctx, 1, 1)), 1);
        }
    }

    inline Vns boolXor(Vns &b) {
        assert(is_bool());
        if (real()) {
            if (b.real()) {
                return Vns(m_ctx, (bool)((bool)(*this) ^ (bool)(b)), 1);
            }
            else {
                if ((UChar)(*this)) {//1 ^
                    return Vns(m_ctx, Z3_mk_eq(m_ctx, b.toZ3Bool(), mkFalse()), 1);
                }
                else {
                    return b;
                }
            }
        }
        else {
            if (b.real()) {
                return  b.boolXor(*this);
            }
            else {
                return Vns(m_ctx, Z3_mk_xor(m_ctx, (Z3_ast)*this, (Z3_ast)b), 1);
            }
        }
    }

    inline Vns translate(Z3_context target_ctx) const
    {
        if (real())
            return Vns(target_ctx, (__m256i)(*this), bitn);
        Z3_ast t = *this;
        dassert(target_ctx != m_ctx);
        return Vns(target_ctx, Z3_translate(m_ctx, t, target_ctx), bitn);
    }

    inline Vns mkFalse() const { return Vns(m_ctx, Z3_mk_false(m_ctx), 1); }

    inline Vns mkTrue() const { return Vns(m_ctx, Z3_mk_true(m_ctx), 1); }

    inline Bool is_bool() const
    {
        dassert(bitn == 1);
        if (m_kind != REAL) {
            return sort_kind() == Z3_BOOL_SORT;
        }
        return True;
    }

#define VnsOperator_eq(op)				   \
	template<typename T>				   \
	inline void operator##op##=(T v) {	   \
		*this = (*this) op (v);			   \
	}
    VnsOperator_eq(/ );
    VnsOperator_eq(%);
    VnsOperator_eq(*);
    VnsOperator_eq(-);
    VnsOperator_eq(+);
    VnsOperator_eq(| );
    VnsOperator_eq(&);
    VnsOperator_eq(^);
    VnsOperator_eq(>> );
    VnsOperator_eq(<< );
#undef VnsOperator_eq

    inline ~Vns() {
        if (m_kind != REAL) {
            Z3_dec_ref(m_ctx, m_ast);
        }
    };

private:
    operator z3::expr() = delete;
    operator z3::expr&() = delete;
    operator z3::expr() const = delete;
    operator z3::expr&() const = delete;
    operator const z3::expr() = delete;
    operator const z3::expr &() = delete;
    operator const z3::expr()const = delete;
    operator const z3::expr &()const = delete;

    operator z3::context() = delete;
    operator z3::context&() = delete;
    operator const z3::context() = delete;
    operator const z3::context&() = delete;
    operator z3::context() const = delete;
    operator z3::context&() const = delete;
    operator const z3::context()const = delete;
    operator const z3::context&()const = delete;


};


static inline Vns ashr(Vns const& a, Vns const& b) {
    if (a.real() || b.real()) {
        switch (a.bitn) {
        case 8: return Vns(a, (SChar)a >> ((UChar)b), 8);
        case 16:return Vns(a, (SShort)a >> ((UChar)b), 16);
        case 32:return Vns(a, (SInt)a >> ((UChar)b), 32);
        case 64:return Vns(a, (SLong)a >> ((UChar)b), 64);
        default:
            return a.ashr((UChar)b);
        }
    }
    else {
        if (a.bitn == b.bitn)
            return Vns(a, Z3_mk_bvashr(a, a, b), a.bitn);
        else if (a.bitn > b.bitn)
            return Vns(a, Z3_mk_bvashr(a, a, b.zext(a.bitn - b.bitn)), a.bitn);
        else
            return Vns(a, Z3_mk_bvashr(a, a.zext(b.bitn - a.bitn), b), a.bitn);
    }
}


#define Macrro_integer(Macrro, op, issigned, ...)				    \
Macrro(op, unsigned char,	issigned, ##__VA_ARGS__);					\
Macrro(op, unsigned short,	issigned, ##__VA_ARGS__);					\
Macrro(op, unsigned int,	issigned, ##__VA_ARGS__);					\
Macrro(op, unsigned long,	issigned, ##__VA_ARGS__);					\
Macrro(op, unsigned long long,	issigned, ##__VA_ARGS__);				\
Macrro(op, char,	issigned, ##__VA_ARGS__);					        \
Macrro(op, signed char,	issigned, ##__VA_ARGS__);					    \
Macrro(op, short,	issigned, ##__VA_ARGS__);					        \
Macrro(op, int,	issigned, ##__VA_ARGS__);								\
Macrro(op, long,	issigned, ##__VA_ARGS__);							\
Macrro(op, long long,	issigned, ##__VA_ARGS__);						\



#define VnsOperator_integer(op, T, issigned)																															\
static inline Vns operator##op##(Vns const &a, T b) {																													\
	if(a.bitn==(sizeof(T)<<3))	return a op Vns(a, b);																													\
	return (a.bitn>(sizeof(T)<<3))? a op Vns(a, b).##issigned##ext(a.bitn-(sizeof(T)<<3)) : a.##issigned##ext((sizeof(T)<<3)-a.bitn) op Vns(a, b);						\
}																																										\
static inline Vns operator##op##(T a, Vns const &b) {																													\
	if(b.bitn==(sizeof(T)<<3))	return Vns(b, a) op b;																													\
	return (b.bitn>(sizeof(T)<<3))? Vns(b, a).##issigned##ext(b.bitn - (sizeof(T) << 3)) op b : Vns(b, a) op b.##issigned##ext((sizeof(T) << 3) - b.bitn);				\
}																																										


#define VnsOperator_integer_opname(op, T, issigned, opname)																												\
static inline Vns opname(Vns const &a, T b) {																															\
	if(a.bitn==(sizeof(T)<<3))	return a op Vns(a, b);																													\
	return (a.bitn>(sizeof(T)<<3))? opname(a , Vns(a, b).##issigned##ext(a.bitn-(sizeof(T)<<3))) :opname( a.##issigned##ext((sizeof(T)<<3)-a.bitn) , Vns(a, b));		\
}																																										\
static inline Vns opname(T a, Vns const &b) {																															\
	if(b.bitn==(sizeof(T)<<3))	return Vns(b, a) op b;																													\
	return (b.bitn>(sizeof(T)<<3))? opname(Vns(b, a).##issigned##ext(b.bitn - (sizeof(T) << 3)) , b) : opname(Vns(b, a) , b.##issigned##ext((sizeof(T) << 3) - b.bitn));\
}

#define VnsOperator_shift_L(op, T, issigned)																										                    \
static inline Vns operator <<(Vns const &a, T b) {																															    \
	return a.shl((UInt)b);																													                            \
}																																										\
static inline Vns operator <<(T a, Vns const &b) {																															    \
	if(b.bitn==(sizeof(T)<<3))	return Vns(b, a) << b;																													\
        if(b.real()){                                                                                                                                                   \
            return Vns(b, a).shl((UInt)b);                                                                                                                              \
        }                                                                                                                                                               \
        else {                                                                                                                                                          \
            return (Vns(b, a) << b.##issigned##ext((sizeof(T) << 3) - b.bitn));                                                                                         \
        }                                                                                                                                                               \
}

#define VnsOperator_shift_R(op, T, issigned)																										                    \
static inline Vns operator >>(Vns const &a, T b) {																															    \
	return a.lshr((UInt)b);																													                            \
}																																										\
static inline Vns operator >>(T a, Vns const &b) {																															    \
    if (((T)-1 > 0)) {                                                                                                                                                  \
        if(b.real()){                                                                                                                                                   \
            return Vns(b, a).lshr((UInt)b);                                                                                                                             \
        }                                                                                                                                                               \
        else {                                                                                                                                                          \
            return (Vns(b, a) >> b.##issigned##ext((sizeof(T) << 3) - b.bitn));                                                                                         \
        }                                                                                                                                                               \
    }                                                                                                                                                                   \
    else {                                                                                                                                                              \
        if(b.real()){                                                                                                                                                   \
            return Vns(b, a).ashr((UInt)b);                                                                                                                             \
        }                                                                                                                                                               \
        else {                                                                                                                                                          \
            return ashr(Vns(b, a) , b.##issigned##ext((sizeof(T) << 3) - b.bitn));                                                                                      \
        }                                                                                                                                                               \
    }                                                                                                                                                                   \
}




#define VnsOperator_bitwishe(op, z3op, issigned) 												\
static inline Vns operator##op##(Vns const &a, Vns const &b) {									\
	if(a.real()&&b.real()){																		\
		switch(a.bitn){																			\
		case 8: return Vns(a, (issigned##Char)a  op (issigned##Char)b, 8);						\
		case 16:return Vns(a, (issigned##Short)a  op(issigned##Short)b, 16);					\
		case 32:return Vns(a, (issigned##Int)a  op(issigned##Int)b, 32);						\
		case 64:return Vns(a, (issigned##Long)a  op (issigned##Long)b, 64);						\
		default:return Vns(a, z3op(a, a, b), a.bitn).simplify();								\
		}																						\
	}																							\
	else {																						\
		return Vns(a, z3op(a, a, b), a.bitn);													\
	}																							\
};																																		

#define VnsOperator_bitshift(op, opname, z3op, issigned) 										\
static inline Vns operator##op##(Vns const &a, Vns const &b) {									\
	if(a.real()&&b.real()){																		\
		switch(a.bitn){																			\
		case 8: return Vns(a, (issigned##Char)a  op (issigned##Char)b, 8);						\
		case 16:return Vns(a, (issigned##Short)a  op(issigned##Short)b, 16);					\
		case 32:return Vns(a, (issigned##Int)a  op(issigned##Int)b, 32);						\
		case 64:return Vns(a, (issigned##Long)a  op (issigned##Long)b, 64);						\
		default:return a.opname((UInt)b);								                        \
		}																						\
	}																							\
	else {																						\
		return Vns(a, z3op(a, a, b), a.bitn);													\
	}																							\
};		

#define VnsOperator_bitwishe_flag(op, z3op, issigned) 											\
static inline Vns operator##op##(Vns const &a, Vns const &b) {									\
	if(a.real()&&b.real()){																		\
		switch(a.bitn){																			\
		case 8: return Vns(a, (issigned##Char)a  op (issigned##Char)b, 1);						\
		case 16:return Vns(a, (issigned##Short)a  op(issigned##Short)b, 1);						\
		case 32:return Vns(a, (issigned##Int)a  op(issigned##Int)b, 1);							\
		case 64:return Vns(a, (issigned##Long)a  op (issigned##Long)b, 1);						\
		default:return Vns(a, z3op(a, a, b), 1).simplify();										\
		}																						\
	}																							\
	else {																						\
		return Vns(a, z3op(a, a, b), 1);														\
	}																							\
};																																		



#define VnsOperator_bitwishe_flag_opname(opname, op, z3op, issigned) 							\
static inline Vns opname(Vns const &a, Vns const &b) {											\
	if(a.real()&&b.real()){																		\
		switch(a.bitn){																			\
		case 8: return Vns(a, (issigned##Char)a  op (issigned##Char)b, 1);						\
		case 16:return Vns(a, (issigned##Short)a  op(issigned##Short)b, 1);						\
		case 32:return Vns(a, (issigned##Int)a  op(issigned##Int)b, 1);							\
		case 64:return Vns(a, (issigned##Long)a  op (issigned##Long)b, 1);						\
		default:return Vns(a, z3op(a, a, b), 1).simplify();										\
		}																						\
	}																							\
	else {																						\
		return Vns(a, z3op(a, a, b), 1);														\
	}																							\
};																																		

VnsOperator_bitwishe(/ , Z3_mk_bvudiv, U);
Macrro_integer(VnsOperator_integer, / , z);
VnsOperator_bitwishe(%, Z3_mk_bvurem, U);
Macrro_integer(VnsOperator_integer, %, z);
VnsOperator_bitwishe(*, Z3_mk_bvmul, U);
Macrro_integer(VnsOperator_integer, *, z);
VnsOperator_bitwishe(-, Z3_mk_bvsub, U);
Macrro_integer(VnsOperator_integer, -, z);
VnsOperator_bitwishe(+, Z3_mk_bvadd, U);
Macrro_integer(VnsOperator_integer, +, z);
VnsOperator_bitwishe(| , Z3_mk_bvor, U);
Macrro_integer(VnsOperator_integer, | , z);
VnsOperator_bitwishe(&, Z3_mk_bvand, U);
Macrro_integer(VnsOperator_integer, &, z);

VnsOperator_bitshift(>> , lshr, Z3_mk_bvlshr, U);
Macrro_integer(VnsOperator_shift_R, >> , z);
VnsOperator_bitshift(<< , shl, Z3_mk_bvshl, U);
Macrro_integer(VnsOperator_shift_L, << , z);

VnsOperator_bitwishe(^, Z3_mk_bvxor, U);
Macrro_integer(VnsOperator_integer, ^, z);


VnsOperator_bitwishe_flag(<= , Z3_mk_bvule, U);
Macrro_integer(VnsOperator_integer, <= , z);
VnsOperator_bitwishe_flag(< , Z3_mk_bvult, U);
Macrro_integer(VnsOperator_integer, < , z);
VnsOperator_bitwishe_flag(>= , Z3_mk_bvuge, U);
Macrro_integer(VnsOperator_integer, >= , z);
VnsOperator_bitwishe_flag(> , Z3_mk_bvugt, U);
Macrro_integer(VnsOperator_integer, > , z);
VnsOperator_bitwishe_flag(== , Z3_mk_eq, U);
Macrro_integer(VnsOperator_integer, == , z);
VnsOperator_bitwishe_flag(!= , Z3_mk_neq, U);
Macrro_integer(VnsOperator_integer, != , z);

VnsOperator_bitwishe_flag_opname(le, <= , Z3_mk_bvsle, S);
Macrro_integer(VnsOperator_integer_opname, <= , s, le);
VnsOperator_bitwishe_flag_opname(lt, < , Z3_mk_bvslt, S);
Macrro_integer(VnsOperator_integer_opname, < , s, lt);
VnsOperator_bitwishe_flag_opname(ge, >= , Z3_mk_bvsge, S);
Macrro_integer(VnsOperator_integer_opname, >= , s, ge);
VnsOperator_bitwishe_flag_opname(gt, > , Z3_mk_bvsgt, S);
Macrro_integer(VnsOperator_integer_opname, > , s, gt);


inline Vns operator!(Vns const &a) {
    if (a.real()) {
        return Vns(a, !(UChar)(a));
    }
    dassert(a.is_bool());
    return Vns(a, Z3_mk_not(a, a), 1);
}

inline Vns operator-(Vns const &a) {
    if (a.real()) {
        switch (a.bitn) {
        case 8: return Vns(a, -(SChar)(a), 8);
        case 16:return Vns(a, -(SShort)(a), 16);
        case 32:return Vns(a, -(SInt)(a), 32);
        case 64:return Vns(a, -(SLong)(a), 64);
        default:return Vns(a, Z3_mk_bvneg(a, a), a.bitn).simplify();
        }
    }
    return Vns(a, Z3_mk_bvneg(a, a), a.bitn);
}

inline Vns operator~(Vns const &a) {
    if (a.real()) {
        switch (a.bitn) {
        case 8: return Vns(a, ~(SChar)(a), 8);
        case 16:return Vns(a, ~(SShort)(a), 16);
        case 32:return Vns(a, ~(SInt)(a), 32);
        case 64:return Vns(a, ~(SLong)(a), 64);
        default:return Vns(a, Z3_mk_bvnot(a, a), a.bitn).simplify();
        }
    }
    return Vns(a, Z3_mk_bvnot(a, a), a.bitn);
}

static inline Vns operator||(Vns const &a, Vns const &b) {
    if (a.real())
        return (UChar(a)) ? a : b;
    Z3_ast args[2] = { a.toZ3Bool(), b.toZ3Bool() };
    return Vns(a, Z3_mk_or(a, 2, args), 1);
};

static inline Vns operator||(bool a, Vns const &b) {
    return Vns(b, a, 1) || b;
};

static inline Vns operator||(Vns const &a, bool b) {
    return a || Vns(a, b, 1);
};

static inline Vns operator&&(Vns const &a, Vns const &b) {
    if (a.real()) {
        return (UChar(a)) ? b : a;
    }
    Z3_ast args[2] = { a.toZ3Bool(), b.toZ3Bool() };
    return Vns(a, Z3_mk_and(a, 2, args), 1);
};

static inline Vns operator&&(Vns const &a, bool b) {
    return a && Vns(a, b, 1);
};

static inline Vns operator&&(bool a, Vns const &b) {
    return Vns(b, a, 1) && b;
};



static inline Vns ite(Vns const & a, Vns const & b, Vns const & c) {
    if (a.real()) {
        if (a.bitn == 1)
            return (((UChar)a) & 1) ? b : c;
        else
            return ((ULong)a & fastMask(a.bitn)) ? b : c;
    }
    return Vns(a, Z3_mk_ite(a, a.toZ3Bool(), b, c), b.bitn);
}


template<typename T>
static inline Vns ashr(Vns const &a, T b) {
    return ashr(a, Vns(a, b));
}

template<typename T>
static inline Vns ashr(T a, Vns const &b) {
    return  ashr(Vns(b, a), b);
}

static inline Vns implies(Vns const& a, Vns const& b) {
    return Vns(a, Z3_mk_implies(a, a.toZ3Bool(), b.toZ3Bool()), 1);
}


static inline std::ostream& operator<<(std::ostream& out, Vns const& n) { return out << (std::string) n; }

#undef VnsOperator_bitwishe 
#undef VnsOperator_bitwishe_flag
#undef VnsOperator_integer 
#undef VnsOperator_bitwishe_flag_opname 
#undef VnsOperator_integer_opname
#undef Macrro_integer
#undef VnsOperator_eq
#undef CP_DATA
#undef VnsOperator_shift_R
#undef VnsOperator_shift_L



#endif



#define TASSERT(v) std::enable_if_t<(v)> * = nullptr
namespace sv {
    template <class _Ty>
    struct type_constant {
        using value_type = std::remove_const<_Ty>::type;
    };

    template <class _Ty1, _Ty1 _Ty2>
    struct value_constant {
        static constexpr _Ty1 value = _Ty2;
    };

    template <class, class, bool>
    constexpr bool _choose_large_type = false;

    template <class _Ty1, class _Ty2>
    constexpr _Ty1 _choose_large_type<_Ty1, _Ty2, true> = (_Ty1)1;

    template <class _Ty1, class _Ty2>
    constexpr _Ty2 _choose_large_type<_Ty1, _Ty2, false> = (_Ty2)0;

    template <class _Ty1, class _Ty2>
    struct large_type : type_constant<decltype(_choose_large_type < _Ty1, _Ty2, sizeof(_Ty1) >= sizeof(_Ty2)>) > {};



    template <bool, class, class>
    constexpr auto _ite_type = false;//error

    template <class _Ty1, class _Ty2>
    constexpr auto _ite_type<true, _Ty1, _Ty2> = (_Ty1)1;

    template <class _Ty1, class _Ty2>
    constexpr auto _ite_type<false, _Ty1, _Ty2> = (_Ty2)1;

    template <bool _Tbool, class _Ty1, class _Ty2>
    struct ite_type : type_constant<decltype(_ite_type<_Tbool, _Ty1, _Ty2>)> {};

    template<class _Rty, bool _Tbool, _Rty _Ty1, _Rty _Ty2>
    struct _ite_val {
        static constexpr _Rty val = 0;
    };

    template<class _Rty, _Rty _Ty1, _Rty _Ty2>
    struct _ite_val<_Rty, true, _Ty1, _Ty2> {
        static constexpr _Rty val = _Ty1;
    };

    template<class _Rty, _Rty _Ty1, _Rty _Ty2>
    struct _ite_val<_Rty, false, _Ty1, _Ty2> {
        static constexpr _Rty val = _Ty2;
    };

    template <class _Rty, bool _Tbool, _Rty _Ty1, _Rty _Ty2>
    struct ite_val : value_constant<_Rty, _ite_val<_Rty, _Tbool, _Ty1, _Ty2>::val > {};


    template <class, class>
    constexpr auto _convert_type = false;

    template <class _Ty1, class _Ty2>
    constexpr auto _convert_type<_Ty1, _Ty2> = (_Ty1)0 + (_Ty1)0;

    template <class _Ty1, class _Ty2>
    struct convert : type_constant<decltype(_convert_type<_Ty1, _Ty2>)> {};





//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    using z3sk = Z3_sort_kind;
    //   temp
    template<
        typename _Tty, int _Tn, z3sk _Tk 
    > class ctype_val;

    //   temp
    template<
        bool _is_signed, int _nbits, z3sk _sort_kind
    > class symbolic;

    ////   bool val
    //template<bool _is_signed, int _nbits>
    //class symbolic<_is_signed, _nbits, Z3_BOOL_SORT>;

    ////   signed Z3_BV_SORT
    //template<int _nbits >
    //class symbolic<true, _nbits, Z3_BV_SORT>;

    ////   UNsigned Z3_BV_SORT
    //template<int _nbits >
    //class symbolic<false, _nbits, Z3_BV_SORT>;

    ////   Z3_FLOATING_POINT_SORT
    //template<int _nbits >
    //class symbolic<false, _nbits, Z3_FLOATING_POINT_SORT>;

    //  VEX TEMP
    class tval;
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

};


namespace sv {

    class sort {
    public:
        Z3_context m_ctx;
        Z3_ast m_sort;
        inline sort(Z3_context ctx, Z3_ast sort) :m_ctx(ctx), m_sort(sort){ Z3_inc_ref(m_ctx, m_sort); }
        inline sort(Z3_context ctx, Z3_sort sort) : m_ctx(ctx), m_sort(reinterpret_cast<Z3_ast>(sort)) { Z3_inc_ref(m_ctx, m_sort); }
        inline operator Z3_ast () const { return m_sort; }
        inline operator Z3_sort () const { return reinterpret_cast<Z3_sort>(m_sort); }
        inline ~sort() { Z3_dec_ref(m_ctx, m_sort); }
    };




    __declspec(align(16))
        class symbol {
        using _CTX_ = size_t;
        using _AST_ = size_t;
        _CTX_ m_ctx : 48;
        _CTX_  : 8;
        _CTX_ m_data_inuse : 8;

        _AST_ m_ast : 48;
        _AST_ m_bits : 16;


        template<typename _ty, int _tn, z3sk _tk> friend class ctype_val;
        template<bool _ts, int _tn, z3sk _tk> friend class symbolic;
        friend class tval;


        inline symbol(Z3_context ctx) : m_ctx((_CTX_)ctx), m_ast((_AST_)0) { }
        inline symbol(Z3_context ctx, int nbits) : m_ctx((_CTX_)ctx), m_ast((_AST_)0), m_bits(nbits) { }
        inline symbol(Z3_context ctx, Z3_ast ast) : m_ctx((_CTX_)ctx), m_ast((_AST_)ast) {
            dassert(ast); 
            Z3_inc_ref(ctx, ast); 
        }
        inline symbol(Z3_context ctx, Z3_ast ast, int nbits) : m_ctx((_CTX_)ctx), m_ast((_AST_)ast), m_bits(nbits) { 
            dassert(ast);
            Z3_inc_ref(ctx, ast); 
        }


        template<class _Ty>
        symbol(Z3_context ctx, _Ty v, struct mk_ast) : m_ctx((_CTX_)ctx) {
            static_assert(std::is_arithmetic<_Ty>::value, "error");
            static_assert(sizeof(_Ty) <= 8, "error");
            Z3_sort zsort = Z3_mk_bv_sort(ctx, sizeof(_Ty) << 3);
            Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            m_ast = (_AST_)Z3_mk_unsigned_int64(ctx, *((uint64_t*)&v), zsort);
            Z3_inc_ref(ctx, (Z3_ast)m_ast);
            Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
        }

        template<class _Ty, TASSERT(sizeof(_Ty) <= 8), TASSERT(std::is_integral<_Ty>::value) >
        symbol(Z3_context ctx, _Ty v, int nbits) : m_ctx((_CTX_)ctx) {
            Z3_sort zsort = Z3_mk_bv_sort(ctx, nbits);
            Z3_inc_ref((Z3_context)m_ctx, reinterpret_cast<Z3_ast>(zsort));
            m_ast = (_AST_)Z3_mk_unsigned_int64(ctx, *((uint64_t*)&v), zsort);
            Z3_inc_ref(ctx, (Z3_ast)m_ast);
            Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
        }


        template<class _Ty, TASSERT(sizeof(_Ty) <= 8), TASSERT(std::is_arithmetic<_Ty>::value) >
        symbol(Z3_context ctx, _Ty v, const sort&s, int nbits) : m_ctx((_CTX_)ctx) {
            m_ast = (_AST_)Z3_mk_unsigned_int64(ctx, *((uint64_t*)&v), s);
            Z3_inc_ref(ctx, (Z3_ast)m_ast);
        }


        template<class _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(!std::is_class<_Ty>::value) >
       symbol(Z3_context ctx, const _Ty& v, const sort& s, int nbits) : m_ctx((_CTX_)ctx) {
            m_ast = (_AST_)_mk_ast(ctx, (uint64_t*)&v, nbits);
            Z3_ast fpa = Z3_mk_fpa_to_fp_bv(ctx, (Z3_ast)m_ast, s);
            Z3_inc_ref(ctx, fpa);
            Z3_dec_ref(ctx, (Z3_ast)m_ast);
            m_ast = (_AST_)fpa;
            _simpify();
        }

        template<class _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(!std::is_class<_Ty>::value)>
        inline symbol(Z3_context ctx, const _Ty& v, int nbits) : m_ctx((_CTX_)ctx) {
            m_ast = (_AST_)_mk_ast(ctx, (uint64_t*)&v, nbits);
            _simpify();
        }


        symbol(Z3_context ctx, uint64_t* v, int nbit) : m_ctx((_CTX_)ctx) {
            m_ast = (_AST_)_mk_ast(ctx, v, nbit);
            _simpify();
        };


        inline sort bool_sort() const { return sort((Z3_context)m_ctx, Z3_mk_bool_sort((Z3_context)m_ctx)); }
        inline sort bv_sort(unsigned ebits) const { return sort((Z3_context)m_ctx, Z3_mk_bv_sort((Z3_context)m_ctx, ebits)); }
        inline sort fpa_sort(unsigned ebits, unsigned sbits) const { return sort((Z3_context)m_ctx, Z3_mk_fpa_sort((Z3_context)m_ctx, ebits, sbits)); }
        template<int n> sort fpa_sort() const = delete;
        template<> inline sort fpa_sort<16>() const { return fpa_sort(5, 11); }
        template<> inline sort fpa_sort<32>() const { return fpa_sort(8, 24); }
        template<> inline sort fpa_sort<64>() const { return fpa_sort(11, 53); }
        template<> inline sort fpa_sort<128>() const { return fpa_sort(15, 113); }


        inline ~symbol() { if (m_ast) Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast); }





        static inline Z3_ast _mk_ast_(Z3_context ctx, uint64_t v, unsigned nb) {
            Z3_sort zsort = Z3_mk_bv_sort(ctx, nb);
            Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            Z3_ast r = Z3_mk_unsigned_int64(ctx, v, zsort);
            Z3_inc_ref(ctx, r);
            Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            return r;
        }

        static inline Z3_ast _mk_ast(Z3_context ctx, const uint64_t* v, unsigned nbit) {
            Z3_ast r = _mk_ast_(ctx, v[(nbit - 1) >> 6], nbit - ALIGN(nbit - 1, 64));
            for (signed i = ((nbit - 1) >> 6) - 1; i >= 0; i--) {
                Z3_ast s = _mk_ast_(ctx, v[i], 64);
                Z3_ast nr = Z3_mk_concat(ctx, r, s);
                Z3_inc_ref(ctx, nr);
                Z3_dec_ref(ctx, s);
                Z3_dec_ref(ctx, r);
                r = nr;
            }
            return r;
        }
        private:
            void _simpify() {
                Z3_ast simp = Z3_simplify((Z3_context)m_ctx, (Z3_ast)m_ast);
                Z3_inc_ref((Z3_context)m_ctx, simp);
                Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                m_ast = (_AST_)simp;
            }
    };

    static sort fpRM(Z3_context m_ctx, IRRoundingMode md) {
        switch (md) {
        case Irrm_NEAREST: { return sort(m_ctx, Z3_mk_fpa_rne(m_ctx)); }
        case Irrm_PosINF: { return sort(m_ctx, Z3_mk_fpa_rtp(m_ctx)); }
        case Irrm_ZERO: { return sort(m_ctx, Z3_mk_fpa_rtz(m_ctx)); }
        case Irrm_NEAREST_TIE_AWAY_0: { return sort(m_ctx, Z3_mk_fpa_rna(m_ctx)); }
        case Irrm_NegINF: { return sort(m_ctx, Z3_mk_fpa_rtn(m_ctx)); }
        default: VPANIC("NOT SUPPPORT");
        }
    }

    inline sort bool_sort(Z3_context m_ctx)  { return sort((Z3_context)m_ctx, Z3_mk_bool_sort((Z3_context)m_ctx)); }
    inline sort bv_sort(Z3_context m_ctx, unsigned ebits)  { return sort((Z3_context)m_ctx, Z3_mk_bv_sort((Z3_context)m_ctx, ebits)); }
    inline sort fpa_sort(Z3_context m_ctx, unsigned ebits, unsigned sbits)  { return sort((Z3_context)m_ctx, Z3_mk_fpa_sort((Z3_context)m_ctx, ebits, sbits)); }
    template<int n> sort fpa_sort(Z3_context m_ctx) = delete;
    template<> inline sort fpa_sort<16>(Z3_context m_ctx)  { return fpa_sort(m_ctx, 5, 11); }
    template<> inline sort fpa_sort<32>(Z3_context m_ctx)  { return fpa_sort(m_ctx, 8, 24); }
    template<> inline sort fpa_sort<64>(Z3_context m_ctx)  { return fpa_sort(m_ctx, 11, 53); }
    template<> inline sort fpa_sort<128>(Z3_context m_ctx)  { return fpa_sort(m_ctx, 15, 113); }
}

namespace sv {
    template<
        typename _Tty,
        int _Tn = ite_val<int, std::is_same<std::decay<_Tty>::type, bool>::value, 1, (sizeof(_Tty) << 3)>::value,
        z3sk _Tk = ite_val<z3sk, std::is_same<std::decay<_Tty>::type, bool>::value, Z3_BOOL_SORT,/**/ ite_val<z3sk, std::is_floating_point<_Tty>::value, Z3_FLOATING_POINT_SORT, Z3_BV_SORT>::value /**/ >::value
    > class ctype_val : protected symbol {
        _Tty m_data;
        template<typename _t1, int _tn, z3sk _tk> friend class ctype_val;
        template<bool _ts, int _tn, z3sk _tk> friend class symbolic;
        friend class tval;
    public:
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value), TASSERT(sizeof(_Ty)<=8)>
        inline ctype_val(Z3_context ctx, _Ty data) :symbol(ctx), m_data(data) {
            static_assert(offsetof(ctype_val<_Tty>, m_data) == 0x10, "error");
            static_assert(_Tn > 0, "error");
        }
        // sse 
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value), TASSERT(sizeof(_Ty) > 8)>
        inline ctype_val(Z3_context ctx,const _Ty& data) :symbol(ctx){
            static_assert(offsetof(ctype_val<_Tty>, m_data) == 0x10, "error");
            static_assert(_Tn > 0, "error");
            *(_Ty*)(&m_data) = data;
        }

        // [ctype] v = ctype_val
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value)>
        inline operator _Ty() const { return (_Ty)m_data; }

        // res
        template<typename _Ty1>
        inline ctype_val(const ctype_val<_Ty1>& b) :symbol((Z3_context)b.m_ctx), m_data(b.m_data) {}

        template<typename _Ty>
        inline void operator=(const ctype_val<_Ty>& b) {
            ctype_val::~ctype_val();
            ctype_val::ctype_val(b);
        }
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value), TASSERT(sizeof(_Ty) <= 8) >
        inline void operator=(_Ty b) {
            ctype_val::~ctype_val();
            m_ast = (_AST_)0;
            m_data = b;
        }
        // sse
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value), TASSERT(sizeof(_Ty) > 8) >
        inline void operator=(const _Ty& b) {
            ctype_val::~ctype_val();
            m_ast = (_AST_)0;
            m_data = b;
        }

        inline operator Z3_context() const { return (Z3_context)m_ctx; }
        //Z3_BV_SORT
        template<z3sk k = _Tk, TASSERT(k == Z3_BV_SORT)>
        operator Z3_ast() const {
            if (!m_ast) 
                const_cast<ctype_val<_Tty>*>(this)->m_ast = (_AST_)_mk_ast((Z3_context)m_ctx, (uint64_t*)&m_data, _Tn);
            return (Z3_ast)m_ast;
        }
        //bool
        template<z3sk k = _Tk, TASSERT(k == Z3_BOOL_SORT)>
        operator Z3_ast() const {
            //struct _Bst { uint8_t bit : 1; uint8_t oth : 7; };
            if (!m_ast) {
                const_cast<ctype_val*>(this)->m_ast = (_AST_)(m_data ? Z3_mk_true((Z3_context)m_ctx) : Z3_mk_false((Z3_context)m_ctx));
                //const_cast<ctype_val*>(this)->m_ast = (_AST_)(((_Bst*)&m_data)->bit ? Z3_mk_true((Z3_context)m_ctx) : Z3_mk_false((Z3_context)m_ctx));
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
            }
            return (Z3_ast)m_ast;
        }

        //float
        template<z3sk k = _Tk, typename _t = _Tty, bool _f = std::is_same<std::decay<_t>::type, float>::value, TASSERT(k == Z3_FLOATING_POINT_SORT), TASSERT(_f)>
        operator Z3_ast() const {
            if (!m_ast) {
                const_cast<ctype_val*>(this)->m_ast = (_AST_)Z3_mk_fpa_numeral_float((Z3_context)m_ctx, m_data, fpa_sort<_Tn>());
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                dassert(m_ast);
            }
            return (Z3_ast)m_ast;
        }
        //double
        template<z3sk k = _Tk, typename _t = _Tty, bool _f = std::is_same<std::decay<_t>::type, double>::value, TASSERT(k == Z3_FLOATING_POINT_SORT && _f)>
        operator Z3_ast() const {
            if (!m_ast) {
                const_cast<ctype_val*>(this)->m_ast = (_AST_)Z3_mk_fpa_numeral_double((Z3_context)m_ctx, m_data, fpa_sort<_Tn>());
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                dassert(m_ast);
            }
            return (Z3_ast)m_ast;
        }

#define OPERATOR_DEFS(op) \
        template<typename _Ty1, z3sk _Tk0 = _Tk, class _Rty = large_type<_Tty, _Ty1>::value_type, TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator op(const ctype_val<_Ty1>& b) const noexcept {\
            return ctype_val<_Rty>((Z3_context)m_ctx, ( _Rty )((_Rty)m_data op(_Rty)b.m_data));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator op(_Ty0 b) const noexcept {\
            return ctype_val<_Tty, _Tn>((Z3_context)m_ctx, ( _Tty )((_Tty)m_data op(_Tty)b));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        inline int operator op(_Ty0 b) const noexcept {\
            static_assert(false, "ctype_val<bool> "#op" num?");\
        }\



        template<typename _Ty1, z3sk _Tk0 = _Tk, class _Rty = large_type<_Tty, _Ty1>::value_type, TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator +(const ctype_val<_Ty1>& b) const noexcept {\
            return ctype_val<_Rty>((Z3_context)m_ctx, ( _Rty )((_Rty)m_data +(_Rty)b.m_data));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator +(_Ty0 b) const noexcept {\
            return ctype_val<_Tty, _Tn>((Z3_context)m_ctx, ( _Tty )((_Tty)m_data +(_Tty)b));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        inline int operator +(_Ty0 b) const noexcept {\
            static_assert(false, "ctype_val<bool> + num?");\
        }\



        //OPERATOR_DEFS(+);
        OPERATOR_DEFS(-);
        OPERATOR_DEFS(*);
        OPERATOR_DEFS(/);
        OPERATOR_DEFS(%);

        OPERATOR_DEFS(| );
        OPERATOR_DEFS(&);
        OPERATOR_DEFS(^);

#undef OPERATOR_DEFS

#define OPERATOR_DEFS_bool(op) \
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 != Z3_BOOL_SORT)> \
        inline auto operator op(const ctype_val<_Ty1>& b) const noexcept { return ctype_val<bool>((Z3_context)m_ctx, m_data op b.m_data); }\
        template<typename _Ty1, z3sk _Tk0 = _Tk,  TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)> \
        inline auto operator op(_Ty1 b) const noexcept { return ctype_val<bool>((Z3_context)m_ctx, m_data op b); }\
        template<typename _Ty1, z3sk _Tk0 = _Tk,  TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)> \
        inline int operator op(_Ty1 b) const noexcept { static_assert(false, "ctype_val(bool) "#op" num ?"); }\


        OPERATOR_DEFS_bool(> );
        OPERATOR_DEFS_bool(< );
        OPERATOR_DEFS_bool(>= );
        OPERATOR_DEFS_bool(<= );
        OPERATOR_DEFS_bool(== );
        OPERATOR_DEFS_bool(!= );

#undef OPERATOR_DEFS_bool

        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator <<(const ctype_val<_Ty1>& b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)(m_data << b.m_data)); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator >>(const ctype_val<_Ty1>& b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)(m_data >> b.m_data)); }


        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator <<(_Ty1 b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)(m_data << b)); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator >>(_Ty1 b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)(m_data >> b)); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 != Z3_BV_SORT)>
        inline int operator <<(_Ty1 b) const noexcept { static_assert(false, "ctype_val£¨not a Z3_BV_SORT£© <<  num ?"); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BV_SORT)>
        inline int operator >>(_Ty1 b) const noexcept { static_assert(false, "ctype_val£¨not a Z3_BV_SORT£© >>  num ?"); }

        inline ~ctype_val() {}
        inline ctype_val translate(Z3_context target_ctx) const { return ctype_val(target_ctx, m_data); }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn <= 8), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %02x >", _Tn, m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 8 && _tn <= 16), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %04x >", _Tn, m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 16 && _tn <= 32), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %08x >", _Tn, m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 32 && _tn <= 64), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %016x >", _Tn, m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 64 && _tn <= 128), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %016x-%016x >", _Tn, ((uint64_t*)&m_data)[1], ((uint64_t*)&m_data)[0]);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 128), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %016x-%016x-%016x-%016x >", _Tn, ((uint64_t*)&m_data)[3], ((uint64_t*)&m_data)[2], ((uint64_t*)&m_data)[1], ((uint64_t*)&m_data)[0]);
            strContent.assign(buffer);
            return str;
        }


        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn == 1), TASSERT(_Tk0 == Z3_BOOL_SORT)>
        std::string str() const {
            std::string str;
            std::string strContent;
            char buffer[] = { "bool < g >" };
            buffer[7] = '0' + m_data;
            strContent.assign(buffer);
            return str;
        }


        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn == 32), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " float< %f >", *(float*)&m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn == 64), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " double< %lf >", *(double*)&m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(!(_tn == 64 || _tn==32)), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " fpa%d< %08x >", m_bits, m_data);
            strContent.assign(buffer);
            return str;
        }
    };


#define OPERATOR_DEFS(op) \
template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT), TASSERT(_Tn < (sizeof(_Ty0)<<3))>\
static auto operator op(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
    return ctype_val<_Ty0>((Z3_context)b, a op (_Ty0)b);\
}\
template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT), TASSERT(_Tn > (sizeof(_Ty0)<<3))>\
static auto operator op(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
    return ctype_val<_Ty0>((Z3_context)b, a op (_Ty0)b);\
}\
template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
static int operator op(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
    static_assert(false, "num "#op" ctype_val<bool>?");\
}

        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT), TASSERT(_Tn < (sizeof(_Ty0)<<3))>\
        static auto operator +(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            return ctype_val<_Ty0>((Z3_context)b, a + (_Ty0)b);\
        }\
        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT), TASSERT(_Tn > (sizeof(_Ty0)<<3))>\
        static auto operator +(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            return ctype_val<_Ty0>((Z3_context)b, a + (_Ty0)b);\
        }\
        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        static int operator +(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            static_assert(false, "num + ctype_val<bool>?");\
        }\

        OPERATOR_DEFS(-);
        OPERATOR_DEFS(*);
        OPERATOR_DEFS(/ );
        OPERATOR_DEFS(%);

        OPERATOR_DEFS(| );
        OPERATOR_DEFS(&);
        OPERATOR_DEFS(^);

#undef OPERATOR_DEFS


#define OPERATOR_DEFS_bool(op) \
template<typename _Ty1, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)> \
static inline auto operator op(_Ty1 a, const ctype_val<_Tty, _Tn, _Tk0>&b) noexcept { return ctype_val<bool>((Z3_context)b.m_ctx, a op b.m_data ); }\
template<typename _Ty1, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)> \
static inline int operator op(_Ty1 a, const ctype_val<_Tty, _Tn, _Tk0>&b) noexcept { static_assert(false, "num "#op" ctype_val(bool) ?"); }


        OPERATOR_DEFS_bool(> );
        OPERATOR_DEFS_bool(< );
        OPERATOR_DEFS_bool(>= );
        OPERATOR_DEFS_bool(<= );
        OPERATOR_DEFS_bool(== );
        OPERATOR_DEFS_bool(!= );

#undef OPERATOR_DEFS_bool

};


namespace sv{


    // c type symbolic val
    template<
        bool _Tsigned,  //is signed value
        int  _Tn,       //nbits
        z3sk _Tk        // ze sort kind
    >
    class symbolic :protected symbol {
        template<bool _ts, int _tn, z3sk _tk> friend class symbolic;
        friend class tval;
    public:
        inline symbolic(Z3_context ctx, Z3_ast ast) :symbol(ctx, ast) { }

        //bool(true/false)
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT)>
        inline symbolic(Z3_context ctx, bool b) : symbol(ctx, b ? Z3_mk_true(ctx) : Z3_mk_false(ctx)) { };

        //same(same)
        template<typename _ty, int _tn, z3sk _tk, TASSERT(_tn == _Tn), TASSERT(_tk == _Tk)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b) { };

        //bool(nbv)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT), TASSERT(_tk == Z3_BV_SORT)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, b.m_data ? Z3_mk_true((Z3_context)b.m_ctx) : Z3_mk_false((Z3_context)b.m_ctx)) { };

        //nbv(bool)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(__Tn <= 64 ), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BOOL_SORT)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, Z3_mk_unsigned_int64((Z3_context)b.m_ctx, b.m_data ? 1 : 0, bv_sort(_Tn))) {
            static_assert(_tn == 1, "err size");
        };

        //bv (bv)  
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(_tn == __Tn), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BV_SORT)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b) { };

        //bv (s bv)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(_tn < __Tn), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BV_SORT), TASSERT(std::is_signed<_ty>::value)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, Z3_mk_sign_ext((Z3_context)b.m_ctx, __Tn - _tn, (Z3_ast)b)) { };

        //bv (u bv)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(_tn < __Tn), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BV_SORT), TASSERT(!std::is_signed<_ty>::value)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, Z3_mk_zero_ext((Z3_context)b.m_ctx, __Tn - _tn, (Z3_ast)b)) { };

        //float
        template<z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(__Tn == 32), TASSERT(__Tk == Z3_FLOATING_POINT_SORT) >
        inline symbolic(Z3_context ctx, float  v) : symbol(ctx, v, fpa_sort<32>(), _Tn) { };
        //double
        template<z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(__Tn == 64), TASSERT(__Tk == Z3_FLOATING_POINT_SORT) >
        inline symbolic(Z3_context ctx, double v) : symbol(ctx, v, fpa_sort<64>(), _Tn) { };
        //floating_point ( v bits[:])
        template<typename _Ty, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT((sizeof(_Ty) << 3) <= _Tn && sizeof(_Ty) < 8), TASSERT(std::is_integral<_Ty>::value), TASSERT(__Tk == Z3_FLOATING_POINT_SORT) >
        inline symbolic(Z3_context ctx, _Ty v, const sort& fp_sort) : symbol(ctx, v, fp_sort, _Tn) { };
        //floating_point large
        template<typename _Ty, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(sizeof(_Ty) > 8), TASSERT(__Tk == Z3_FLOATING_POINT_SORT) >
        inline symbolic(Z3_context ctx, const _Ty& v, const sort& fp_sort) : symbol(ctx, v, fp_sort, _Tn) { };


        //bv(integral)
        template<typename _Ty, z3sk __Tk = _Tk, TASSERT((sizeof(_Ty) << 3) <= _Tn), TASSERT(std::is_integral<_Ty>::value), TASSERT(__Tk == Z3_BV_SORT) >
        inline symbolic(Z3_context ctx, _Ty v) : symbol(ctx, (ite_type<std::is_signed<_Ty>::value, int64_t, uint64_t>::value_type) v, _Tn) { };

        //bv(sse)
        template<typename _Ty, z3sk __Tk = _Tk, TASSERT((sizeof(_Ty) > 8)), TASSERT((sizeof(_Ty) << 3) == _Tn), TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic(Z3_context ctx, const _Ty& v) : symbol(ctx, v, _Tn) { };

        inline symbolic(const symbolic& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b.m_ast) { }
        
        template<typename _Ty, int _tn, z3sk _tk>
        inline void operator =(const ctype_val<_Ty, _tn, _tk>& b) {
            this->symbolic::~symbolic();
            this->symbolic::symbolic(b);
        }
        template<bool _signed, int _tn, z3sk _tk>
        inline void operator =(const symbolic<_signed, _tn, _tk>& b) {
            this->symbolic::~symbolic();
            this->symbolic::symbolic(b);
        }

        inline operator Z3_context() const { return (Z3_context)m_ctx; }
        inline operator Z3_ast() const { return (Z3_ast)m_ast; }


        template<bool _Resig, int _extn, z3sk __Tk = _Tk, bool _Ts = _Tsigned, TASSERT(!_Ts), TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<_Resig, _Tn + _extn, _Tk> ext() const noexcept {
            static_assert(_extn > 0, "err size");
            return symbolic<_Resig, _Tn + _extn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_zero_ext((Z3_context)m_ctx, _extn, (Z3_ast)m_ast));
        }

        template<bool _Resig, int _extn, z3sk __Tk = _Tk, bool _Ts = _Tsigned, TASSERT(_Ts), TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<_Resig, _Tn + _extn, _Tk> ext() const noexcept {
            static_assert(_extn > 0, "err size");
            return symbolic<_Resig, _Tn + _extn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_sign_ext((Z3_context)m_ctx, _extn, (Z3_ast)m_ast));
        }












#define TEMP_OPERATOR_BITWISHE_NO_ALIGN(op)\
        template<bool _ts, int _tn, TASSERT(_tn < _Tn)>                                                                                    \
        inline auto operator op(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {                                                  \
            return *this op b.ext<_ts, _Tn - _tn>();                                                                                       \
        }                                                                                                                                  \
        template<bool _ts, int _tn, TASSERT(_tn > _Tn)>                                                                                    \
        inline auto operator op(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {                                                  \
            return ext<_Tsigned, _tn - _Tn>() op b;                                                                                        \
        }                                                                                                                                  \
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>                           \
        inline auto operator op(_Ty v) {                                                                                                   \
            return *this op symbolic<std::is_signed<_Ty>::value, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, v);                                   \
        };


#define TEMP_OPERATOR_BITWISHE(op, z3_op)\
        template<bool _ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>                                                                   \
        inline auto operator op(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {                                                  \
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, z3_op((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }                                                                                                                                 

        //add show 
        /*template<bool _ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator +(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvadd((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }
        template<bool _ts, int _tn, TASSERT(_tn < _Tn)>
        inline auto operator +(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {
            return *this + b.ext<_ts, _Tn - _tn>();
        }
        template<bool _ts, int _tn, TASSERT(_tn > _Tn)>
        inline auto operator +(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {
            return ext<_Tsigned, _tn - _Tn>() + b;
        }
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator +(_Ty v) {
            return *this + symbolic<std::is_signed<_Ty>::value, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, v);
        };*/



        TEMP_OPERATOR_BITWISHE(+, Z3_mk_bvadd);
        TEMP_OPERATOR_BITWISHE(-, Z3_mk_bvsub);
        TEMP_OPERATOR_BITWISHE(*, Z3_mk_bvmul);
        TEMP_OPERATOR_BITWISHE(| , Z3_mk_bvor);
        TEMP_OPERATOR_BITWISHE(&, Z3_mk_bvand);
        TEMP_OPERATOR_BITWISHE(^, Z3_mk_bvxor);

        TEMP_OPERATOR_BITWISHE_NO_ALIGN(+);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(-);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(*);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(|);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(&);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(^);



#define TEMP_OPERATOR_BITWISHE_SIGN(op, z3_sop, z3_uop)\
        template<bool _ts, bool __Ts = _Tsigned,  z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(__Ts)>                                     \
        inline auto operator op(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {                                                          \
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, z3_sop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       \
        }                                                                                                                                          \
                                                                                                                                                   \
        template<bool _ts, bool __Ts = _Tsigned, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(!__Ts)>                                     \
        inline auto operator op(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {                                                          \
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, z3_uop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       \
        }                                                                                                                                          \




        TEMP_OPERATOR_BITWISHE_SIGN(/ , Z3_mk_bvsdiv, Z3_mk_bvudiv);
        TEMP_OPERATOR_BITWISHE_SIGN(%, Z3_mk_bvsrem, Z3_mk_bvurem);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(/ );
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(%);

        


        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator <<(const symbolic<false, _Tn, Z3_BV_SORT>& b) const noexcept {
            return symbolic<_Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvshl((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }

        template<int _tn, TASSERT(_tn < _Tn)>
        inline auto operator <<(const symbolic<false, _tn, Z3_BV_SORT>& b) const noexcept {
            return *this << b.ext<false, _Tn - _tn>();
        }
        template<int _tn, TASSERT(_tn > _Tn)>
        inline auto operator <<(const symbolic<false, _tn, Z3_BV_SORT>& b) const noexcept {
            return ext<_Tsigned, _tn - _Tn>() << b;
        }
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), TASSERT(!std::is_signed<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator <<(_Ty v) {
            return *this << symbolic<false, Z3_BV_SORT>((Z3_context)m_ctx, v);
        };





        template<bool __Ts = _Tsigned,  z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(__Ts)>                                     
        inline auto operator >>(const symbolic<false, _Tn, Z3_BV_SORT>& b) const noexcept {                                                          
            return symbolic<_Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvashr((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       
        }                                                                                                                                         
        template<bool __Ts = _Tsigned, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(!__Ts)>                                     
        inline auto operator >>(const symbolic<false, _Tn, Z3_BV_SORT>& b) const noexcept {
            return symbolic<_Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvlshr((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       
        }

        template<int _tn, TASSERT(_tn < _Tn)>
        inline auto operator >>(const symbolic<false, _tn, Z3_BV_SORT>& b) const noexcept {
            return *this >> b.ext<false, _Tn - _tn>();
        }
        template<int _tn, TASSERT(_tn > _Tn)>
        inline auto operator >>(const symbolic<false, _tn, Z3_BV_SORT>& b) const noexcept {
            return ext<_Tsigned, _tn - _Tn>() >> b;
        }
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), TASSERT(!std::is_signed<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator >>(_Ty v) {
            return *this >> symbolic<false, Z3_BV_SORT>((Z3_context)m_ctx, v);
        };







        template<bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator ==(const symbolic<_Ts, _Tn, Z3_BV_SORT>& b) const noexcept {
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, Z3_mk_eq((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }
        template<bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator !=(const symbolic<_Ts, _Tn, Z3_BV_SORT>& b) const noexcept {
            return ! symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, Z3_mk_eq((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(== ); 
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(!= ); 




#define TEMP_OPERATOR_BITWISHE_COMPARE(op, z3_sop, z3_uop)\
        template<bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(_Ts||_Tsigned)>\
        inline auto operator op(const symbolic<_Ts, _Tn, Z3_BV_SORT>& b) const noexcept {\
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, z3_sop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }\
        template<bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(!(_Ts||_Tsigned))>\
        inline auto operator op(const symbolic<_Ts, _Tn, Z3_BV_SORT>& b) const noexcept {\
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, z3_uop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }\
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(op)


        //ule
        TEMP_OPERATOR_BITWISHE_COMPARE(<= , Z3_mk_bvsle, Z3_mk_bvule);
        //ult
        TEMP_OPERATOR_BITWISHE_COMPARE(< , Z3_mk_bvslt, Z3_mk_bvult);
        //uge
        TEMP_OPERATOR_BITWISHE_COMPARE(>= , Z3_mk_bvsge, Z3_mk_bvuge);
        //ugt
        TEMP_OPERATOR_BITWISHE_COMPARE(> , Z3_mk_bvsgt, Z3_mk_bvugt);



        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        auto operator -() {
            return symbolic<_Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvneg((Z3_context)m_ctx, (Z3_ast)m_ast));
        }


#undef TEMP_OPERATOR_BITWISHE
#undef TEMP_OPERATOR_BITWISHE_SIGN
#undef TEMP_OPERATOR_BITWISHE_COMPARE
#undef TEMP_OPERATOR_BITWISHE_NO_ALIGN



#define TEMP_OPERATOR_FP(op, z3_op)\
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>\
        inline auto op(const sort& rm, const symbolic<true, _Tn, Z3_FLOATING_POINT_SORT>& b) const noexcept {\
            return symbolic<true, _Tn, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, z3_op((Z3_context)m_ctx, rm, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }\
        template<class _Ty, TASSERT(std::is_floating_point<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>\
        inline auto op(const sort& rm, _Ty v) {\
            return this->op(rm, symbolic<true, _Tn, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, v));\
        };\

        TEMP_OPERATOR_FP(add, Z3_mk_fpa_add);
        TEMP_OPERATOR_FP(sub, Z3_mk_fpa_sub);
        TEMP_OPERATOR_FP(mul, Z3_mk_fpa_mul);
        TEMP_OPERATOR_FP(div, Z3_mk_fpa_div);


#undef TEMP_OPERATOR_FP





        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        auto operator -() {
            return symbolic<_Tsigned, _Tn, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_neg((Z3_context)m_ctx, (Z3_ast)m_ast));
        }


        //bv -> ieee fpa
        template<unsigned ebits, unsigned sbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> tofpa() const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_bv((Z3_context)m_ctx, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };
        //fpa -> ieee bv
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<false, _Tn, Z3_BV_SORT> tobv() const {
            return symbolic<false, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_ieee_bv((Z3_context)m_ctx, (Z3_ast)m_ast));
        };
        //  signed int bv -> fp
        template<unsigned ebits, unsigned sbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> sInteger2fpa(const sort& rm) const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_signed((Z3_context)m_ctx, rm, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };
        //unsigned int bv -> fp
        template<unsigned ebits, unsigned sbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> uInteger2fpa(const sort& rm) const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_unsigned((Z3_context)m_ctx, rm, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };
        //fp ->   signed int(bv)
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<true , _Tn, Z3_BV_SORT> toInteger_sbv(const sort& rm) const {
            return symbolic<true, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_sbv((Z3_context)m_ctx, rm, (Z3_ast)m_ast));
        };
        //fp -> unsigned int (bv)
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<false, _Tn, Z3_BV_SORT> toIinteger_ubv(const sort& rm) const {
            return symbolic<false, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_ubv((Z3_context)m_ctx, rm, (Z3_ast)m_ast));
        };
        //fp -> fp
        template<unsigned ebits, unsigned sbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> fpa2fpa(const sort& rm) const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_float((Z3_context)m_ctx, rm, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };




        ~symbolic() {}



        inline symbolic translate(Z3_context target_ctx) const { return symbolic(target_ctx, Z3_translate((Z3_context)m_ctx, (Z3_ast)m_ast, target_ctx)); }

        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT)>
        symbolic<false, 1, Z3_BOOL_SORT> implies(const symbolic<false, 1, Z3_BOOL_SORT>& b) const {
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, Z3_mk_implies((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }
        //if
        template<bool _ts, int _tn, z3sk _tk, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT)>
        symbolic<_ts, _tn, _tk> ite(const symbolic<_ts, _tn, _tk>& a, const symbolic<_ts, _tn, _tk>& b) const {
            return symbolic<_ts, _tn, _tk>((Z3_context)m_ctx, Z3_mk_ite((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)a.m_ast, (Z3_ast)b.m_ast));
        }

        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " BS%d < ", bitn);
            strContent.assign(buffer);
            str.append(strContent);
            strContent.assign(Z3_ast_to_string(m_ctx, m_ast));
            str.append(strContent);
            strContent.assign(" >");
            str.append(strContent);
            return str;
        }

    private:
    };
};
    
namespace sv{
    class tval :protected symbol {
        uint64_t m_data[4];
    public:
        inline tval(Z3_context ctx) :symbol(ctx, -1) {
            m_data_inuse = false;
        }
        inline tval() : symbol((Z3_context)nullptr, -1) {
            m_data_inuse = false;
        }
        inline tval(Z3_context ctx, Z3_ast s, int bits) : symbol(ctx, s, bits) {
            m_data_inuse = false;
        }
        // translate a real bv
        inline tval(Z3_context target_ctx, const tval& b) : symbol(target_ctx, b.m_bits) {
            assert(b.m_data_inuse == true);
            m_data_inuse = true;
            if (b.m_bits <= 8) {
                m_data[0] = b.m_data[0];
            }
            else {
                *(__m256i*)m_data = _mm256_load_si256((__m256i*)b.m_data);
            }
        }
        inline tval(const tval& b) : symbol((Z3_context)b.m_ctx, b.m_ast, b.m_bits) {
            m_data_inuse = b.m_data_inuse;
            if (m_data_inuse) {
                if (b.m_bits <= 8) {
                    m_data[0] = b.m_data[0];
                }
                else {
                    *(__m256i*)m_data = _mm256_load_si256((__m256i*)b.m_data);
                }
            }
        }
        template<typename _Ty, std::enable_if_t<std::is_arithmetic<_Ty>::value> * = nullptr>
        inline tval(Z3_context ctx, _Ty data) :symbol(ctx, (sizeof(_Ty) << 3)) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            *(_Ty*)m_data = data;
            m_data_inuse = true;
        }

        template<typename _Ty, std::enable_if_t<std::is_arithmetic<_Ty>::value>* = nullptr>
        inline tval(Z3_context ctx, _Ty data, int bits) :symbol(ctx, bits) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            *(_Ty*)m_data = data;
            m_data_inuse = true;
        }

        template<typename _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(!std::is_class<_Ty>::value)>
        inline tval(Z3_context ctx, const _Ty& data, int bits) :symbol(ctx, bits) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            static_assert(sizeof(_Ty) <= 0x20, "error _TY");
            *(_Ty*)m_data = data;
            m_data_inuse = true;
        }

        inline tval(Z3_context ctx, bool data) :symbol(ctx, 1) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            *(bool*)m_data = data;
            m_data_inuse = true;
        }

        template<typename _Ty, int _tn, z3sk _tk>
        inline tval(const ctype_val<_Ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, _tn) {
            static_assert(_tn <= 0x100, "error _TY");
            static_assert((sizeof(_Ty) << 3) >= _tn, "error");
            *(_Ty*)m_data = b.m_data;
            m_data_inuse = true;
        }

        template<bool _ts, int _tn, z3sk _tk>
        inline tval(const symbolic<_ts, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b.m_ast, _tn) {
            m_data_inuse = false;
        }

        inline tval(Z3_context ctx, const IRConst* con) :symbol(ctx)
        {
            m_data_inuse = true;
            switch (con->tag) {
            case Ico_U1:   m_bits = 1;  *(bool*)m_data = *(bool*)&(con->Ico.U1); return;
            case Ico_U8:   m_bits = 8;  *(uint8_t*)m_data= *(uint8_t*)&(con->Ico.U8); return;
            case Ico_U16:  m_bits = 16; *(uint16_t*)m_data = *(uint16_t*)&(con->Ico.U16); return;

            case Ico_U32:  
            case Ico_F32:  
            case Ico_F32i: m_bits = 32; *(uint32_t*)m_data = con->Ico.U32; return;

            case Ico_F64:  
            case Ico_F64i: 
            case Ico_U64:  m_bits = 64; *(uint64_t*)m_data = *(uint64_t*)&(con->Ico.U64); return;

            case Ico_V128: m_bits = 128; *(__m128i*)m_data = _mm_set1_epi16(con->Ico.V128); break;
            case Ico_V256: m_bits = 256; *(__m256i*)m_data = _mm256_set1_epi32(con->Ico.V256); break;
            default: VPANIC("tIRConst");
            }
        }


        template<typename _Ty, int _tn, z3sk _tk >
        inline void operator=(const ctype_val<_Ty, _tn, _tk>& b) {
            this->~tval();
            this->tval::tval(b);
        }

        template<bool _ts, int _tn, z3sk _tk>
        inline void operator=(const symbolic<_ts, _tn, _tk>& b) {
            this->~tval();
            this->tval::tval(b);
        }

        inline void operator=(const tval& b) {
            this->~tval();
            this->tval::tval(b);
        }

        template<typename _Ty, int _tn, z3sk _tk>
        operator ctype_val<_Ty, _tn, _tk>&() {
            return *reinterpret_cast<ctype_val<_Ty, _tn, _tk>*>(this);
        }

        template<bool _ts, int _tn, z3sk _tk>
        operator symbolic<_ts, _tn, _tk>& () {
            return *reinterpret_cast<symbolic<_ts, _tn, _tk>*>(this);
        }


        inline constexpr operator Z3_context() const { return (Z3_context)m_ctx; }

        inline bool symb() const { return m_data_inuse == false; }
        inline bool real() const { return m_data_inuse; }
        

        inline ~tval() {};
        inline tval translate(Z3_context target_ctx) const {
            if (m_data_inuse) {
                return tval(target_ctx, *this);
            }
            else {
                return tval(target_ctx, Z3_translate((Z3_context)m_ctx, (Z3_ast)m_ast, target_ctx), (int)m_bits);
            }
        }

        std::string str() const {
            if (real()) {
                std::string str;
                char buff[0x80];
                switch (m_bits) {
                case 1:   snprintf(buff, sizeof(buff), " val%d( %d )", m_bits, (*(bool*)m_data) & 1); break;
                case 8:   snprintf(buff, sizeof(buff), " val%d( %02x )", m_bits, *(uint8_t*)m_data); break;
                case 16:  snprintf(buff, sizeof(buff), " val%d( %04x )", m_bits, *(uint16_t*)m_data); break;
                case 32:  snprintf(buff, sizeof(buff), " val%d( %08x )", m_bits, *(uint32_t*)m_data); break;
                case 64:  snprintf(buff, sizeof(buff), " val%d( %016llx )", m_bits, *(uint64_t*)m_data); break;
                case 128: snprintf(buff, sizeof(buff), " val%d( %016llx %016llx )", m_bits, m_data[1], m_data[0]); break;
                case 256: snprintf(buff, sizeof(buff), " val%d( %016llx %016llx %016llx %016llx )", m_bits, m_data[3], m_data[2], m_data[1], m_data[0]); break;
                default:  snprintf(buff, sizeof(buff), " val%d( %016llx %016llx %016llx %016llx )", m_bits, m_data[3], m_data[2], m_data[1], m_data[0]); break;
                }
                str.assign(buff);
                return str;
            }
            else {
                std::string str;
                char buff[0x80];
#if 0
                std::string strContent;
                snprintf(buff, sizeof(buff), " BS%d < ", bitn);
                strContent.assign(buff);
                str.append(strContent);
                strContent.assign(Z3_ast_to_string(m_ctx, m_ast));
                str.append(strContent);
                strContent.assign(" >");
                str.append(strContent);
                return str;
#else
                snprintf(buff, sizeof(buff), " BVS %d < \\%p/ >  ", m_bits, m_ast);
                str.assign(buff);
                return str;
#endif
            }
        }
    };
};

using cBool = sv::ctype_val<bool>;
using cbool = sv::ctype_val<bool>;
using cUChar = sv::ctype_val<UChar>;
using cChar = sv::ctype_val<Char>;
using cUShort = sv::ctype_val<UShort>;
using cShort = sv::ctype_val<Short>;
using cint = sv::ctype_val<int>;
using cunsigned = sv::ctype_val<unsigned>;
using csigned = sv::ctype_val<signed>;
using cInt = sv::ctype_val<Int>;
using cUInt = sv::ctype_val<UInt>;
using cULong = sv::ctype_val<ULong>;
using cLong = sv::ctype_val<Long>;
using csize_t = sv::ctype_val<size_t>;
using cfloat = sv::ctype_val<float>;
using cdouble = sv::ctype_val<double>;
using tval = sv::tval;

using sbool = sv::symbolic<false, 1, Z3_BOOL_SORT>;
template<int nbits> using sbval = sv::symbolic< true, nbits, Z3_BV_SORT>;
template<int nbits> using ubval = sv::symbolic<false, nbits, Z3_BV_SORT>;
template<int nbits> using fpval = sv::symbolic< true, nbits, Z3_FLOATING_POINT_SORT>;
template<int nbits> using sfloat = sv::symbolic< true, 32, Z3_FLOATING_POINT_SORT>;
template<int nbits> using sdouble = sv::symbolic< true, 64, Z3_FLOATING_POINT_SORT>;

template<bool _ts, int _tn, sv::z3sk _tk>
inline sv::symbolic<_ts, _tn, _tk> ite( const sbool& _if, const sv::symbolic<_ts, _tn, _tk>& a, /*else*/  const sv::symbolic<_ts, _tn, _tk>& b) { return _if.ite(a, b); }
static inline sbool implies(sbool const& a, sbool const& b) { return a.implies(b); }

template<bool _ts, int _tn, sv::z3sk _tk> 
static inline std::ostream& operator<<(std::ostream& out, sv::symbolic<_ts, _tn, _tk> const& n) { return out << n.str(); }
template<class _Tty> 
static inline std::ostream& operator<<(std::ostream& out, sv::ctype_val<_Tty> const& n) { return out << n.str(); }
static inline std::ostream& operator<<(std::ostream& out, sv::tval const& n) { return out << n.str(); }


#endif // _Vns_H_