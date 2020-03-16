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

    inline Vns(Z3_context ctx, IRConst *con) :
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
    inline Vns(z3::context const &ctx, IRConst *con) :
        Vns((Z3_context)ctx, con) {};

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

#endif // _Vns_H_