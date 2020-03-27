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
#define UNDEFREG
#include "register.h"

using namespace TR;



__m256i RegisterStatic::m32_fast[33];
__m256i RegisterStatic::m32_mask_reverse[33];

RegisterStatic::RegisterStatic(){
    __m256i m32 = _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19);
    for (int i = 0; i <= 32; i++) {
        m32_fast[i] = m32;
        for (int j = i; j <= 32; j++) {
            m32_fast[i].m256i_i8[j] = 0;
        }
        m32_mask_reverse[i] = _mm256_setzero_si256();
        memset(&m32_mask_reverse[i].m256i_i8[i], -1ul, 32 - i);
    }
}

void RegisterStatic::setfast(void* fast_ptr, UInt __nbytes) {
    if ((__nbytes) <= 8) {
        if ((__nbytes) == 8) {
            SET8(fast_ptr, 0x0807060504030201);
        }
        else {
            __asm__(
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
                : [out] "=r"(GET8((fast_ptr)))
                : [fast] "r"(GET8((fast_ptr))), [nbytes] "r"((UChar)(__nbytes))
                : "rax", "rbx", "rcx"
            );
        }
    }
    else if ((__nbytes) <= 16) {
        _mm_store_si128(
            (__m128i*)(fast_ptr),
            _mm_or_si128(
                _mm_and_si128(
                    GET16((fast_ptr)),
                    GET16(&m32_mask_reverse[__nbytes])
                ),
                GET16(&m32_fast[__nbytes])
            )
        );
    }
    else {
        _mm256_store_si256(
            (__m256i*)(fast_ptr),
            _mm256_or_si256(
                _mm256_and_si256(
                    GET32((fast_ptr)),
                    m32_mask_reverse[__nbytes]
                ),
                m32_fast[__nbytes]
            )
        );
    }
};




//取值函数。将多个ast和真值组合为一个ast
#ifdef USE_HASH_AST_MANAGER
Z3_ast TR::Reg2Ast(int nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX &m_ast, z3::vcontext& ctx) {
#else
Z3_ast TR::Reg2Ast(int nbytes, UChar* m_bytes, UChar* m_fastindex, Z3_ast* m_ast, z3::vcontext & ctx) {
#endif
    vassert(nbytes <= 8);
    ULong scan = GET8(m_fastindex);
    Z3_ast result;
    DWORD index;
    Z3_ast reast;
    if (_BitScanReverse64(&index, scan & fastMask(nbytes << 3))) {
        auto offset = (index >> 3);
        Char relen = nbytes - offset - 1;
        auto fast = m_fastindex[offset];
        if (relen) {
            nbytes -= relen;
            auto zsort = Z3_mk_bv_sort(ctx, relen << 3);
            Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            reast = Z3_mk_unsigned_int64(ctx, GET8(m_bytes + nbytes), zsort);
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
            if (m_fastindex[nbytes] >> 1) {
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
        reast = Z3_mk_unsigned_int64(ctx, GET8(m_bytes), zsort);
        Z3_inc_ref(ctx, reast);
        Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
        return reast;
    }
    while (nbytes > 0) {
        if (_BitScanReverse64(&index, scan & fastMask(nbytes << 3))) {
            auto offset = index >> 3;
            Char relen = nbytes - offset - 1;
            auto fast = m_fastindex[offset];
            if (relen) {
                nbytes -= relen;
                auto zsort = Z3_mk_bv_sort(ctx, relen << 3);
                Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
                reast = Z3_mk_unsigned_int64(ctx, GET8(m_bytes + nbytes), zsort);
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
            reast = Z3_mk_unsigned_int64(ctx, GET8(m_bytes), zsort);
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


class Translate {
    z3::vcontext& m_toctx;
    Z3_ast m_ast;
public:
    inline Translate(z3::vcontext& ctx, z3::vcontext& toctx, Z3_ast s):
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

#ifdef USE_HASH_AST_MANAGER
Z3_ast TR::Reg2Ast(int nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX& m_ast, z3::vcontext& ctx, z3::vcontext& toctx) {
#else
Z3_ast TR::Reg2Ast(int nbytes, UChar * m_bytes, UChar * m_fastindex, Z3_ast * m_ast, z3::vcontext & ctx, z3::vcontext & toctx) {
#endif
    vassert(nbytes <= 8);
    ULong scan = GET8(m_fastindex);
    Z3_ast result;
    DWORD index;
    Z3_ast reast;
    if (_BitScanReverse64(&index, scan & fastMask(nbytes << 3))) {
        auto offset = (index >> 3);
        Char relen = nbytes - offset - 1;
        auto fast = m_fastindex[offset];
        if (relen) {
            nbytes -= relen;
            auto zsort = Z3_mk_bv_sort(toctx, relen << 3);
            Z3_inc_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
            reast = Z3_mk_unsigned_int64(toctx, GET8(m_bytes + nbytes), zsort);
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
            if (m_fastindex[nbytes] >> 1) {
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
        reast = Z3_mk_unsigned_int64(toctx, GET8(m_bytes), zsort);
        Z3_inc_ref(toctx, reast);
        Z3_dec_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
        return reast;
    }
    while (nbytes > 0) {
        if (_BitScanReverse64(&index, scan & fastMask(nbytes << 3))) {
            auto offset = index >> 3;
            Char relen = nbytes - offset - 1;
            auto fast = m_fastindex[offset];
            if (relen) {
                nbytes -= relen;
                auto zsort = Z3_mk_bv_sort(toctx, relen << 3);
                Z3_inc_ref(toctx, reinterpret_cast<Z3_ast>(zsort));
                reast = Z3_mk_unsigned_int64(toctx, GET8(m_bytes + nbytes), zsort);
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
            reast = Z3_mk_unsigned_int64(toctx, GET8(m_bytes), zsort);
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
    Z3_ast reast;
    if (nbit <= 64) {
        auto zsort = Z3_mk_bv_sort(ctx, nbit);
        Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
        reast = Z3_mk_unsigned_int64(ctx, GET8(data), zsort);
        Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
        Z3_inc_ref(ctx, reast);
    }
    else if (nbit <= 128) {
        Vns re(ctx, _mm_loadu_si128((__m128i*)data), nbit);
        reast = re;
        Z3_inc_ref(ctx, reast);
    }
    else if (nbit <= 256) {
        Vns re(ctx, _mm256_loadu_si256((__m256i*)data), nbit);
        reast = re;
        Z3_inc_ref(ctx, reast);
    }
    else {
        return nullptr;
    }
    //vassert(Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, reast)) == nbit);
    return reast;
}

//取值函数。将多个ast和真值组合为一个ast
#ifdef USE_HASH_AST_MANAGER
Z3_ast TR::Reg2AstSSE(int nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX& m_ast, z3::vcontext& ctx) {
#else
Z3_ast TR::Reg2AstSSE(int nbytes, UChar * m_bytes, UChar * m_fastindex, Z3_ast * m_ast, z3::vcontext & ctx) {
#endif
    vassert(nbytes <= 32);
    UInt scan = ~_mm256_movemask_epi8(_mm256_cmpeq_epi8(_mm256_setzero_si256(), _mm256_loadu_si256((__m256i*)m_fastindex)));
    Z3_ast result;
    DWORD index;
    Z3_ast reast;
    if (_BitScanReverse64(&index, scan & fastMask(nbytes))) {
        Char relen = nbytes - index - 1;
        auto fast = m_fastindex[index];
        if (relen) {
            nbytes -= relen;
            reast = mk_large_int(ctx, m_bytes + nbytes, relen << 3);
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
            if (m_fastindex[nbytes] >> 1) {
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
        return mk_large_int(ctx, m_bytes, nbytes << 3);
    }
    while (nbytes > 0) {
        if (_BitScanReverse64(&index, scan & fastMask(nbytes))) {
            Char relen = nbytes - index - 1;
            auto fast = m_fastindex[index];
            if (relen) {
                nbytes -= relen;
                reast = mk_large_int(ctx, m_bytes + nbytes, relen << 3);
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
            reast = mk_large_int(ctx, m_bytes, nbytes << 3);
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
Z3_ast TR::Reg2AstSSE(int nbytes, UChar * m_bytes, UChar * m_fastindex, AstManager::AstManagerX & m_ast, z3::vcontext & ctx, z3::vcontext & toctx) {
#else
Z3_ast TR::Reg2AstSSE(int nbytes, UChar * m_bytes, UChar * m_fastindex, Z3_ast * m_ast, z3::vcontext & ctx, z3::vcontext & toctx) {
#endif
    vassert(nbytes <= 32);
    UInt scan = ~_mm256_movemask_epi8(_mm256_cmpeq_epi8(_mm256_setzero_si256(), _mm256_loadu_si256((__m256i*)m_fastindex)));
    Z3_ast result;
    DWORD index;
    Z3_ast reast;
    if (_BitScanReverse64(&index, scan & fastMask(nbytes))) {
        Char relen = nbytes - index - 1;
        auto fast = m_fastindex[index];
        if (relen) {
            nbytes -= relen;
            reast = mk_large_int(toctx, m_bytes + nbytes, relen << 3);
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
            if (m_fastindex[nbytes] >> 1) {
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
        return mk_large_int(toctx, m_bytes, nbytes << 3);
    }
    while (nbytes > 0) {
        if (_BitScanReverse64(&index, scan & fastMask(nbytes))) {
            Char relen = nbytes - index - 1;
            auto fast = m_fastindex[index];
            if (relen) {
                nbytes -= relen;
                reast = mk_large_int(toctx, m_bytes + nbytes, relen << 3);
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
            reast = mk_large_int(toctx, m_bytes, nbytes << 3);
            Z3_ast newresult = Z3_mk_concat(toctx, result, reast);
            Z3_inc_ref(toctx, newresult);
            Z3_dec_ref(toctx, reast);
            Z3_dec_ref(toctx, result);
            return newresult;
        }
    }
    return result;
}
