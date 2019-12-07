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
#include "Register.hpp"

//取值函数。将多个ast和真值组合为一个ast
#ifdef USE_HASH_AST_MANAGER
Z3_ast Reg2Ast(Char nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX &m_ast, TRcontext& ctx) {
#else
Z3_ast Reg2Ast(Char nbytes, UChar* m_bytes, UChar* m_fastindex, Z3_ast* m_ast, TRcontext & ctx) {
#endif
    ULong fast_index = GET8(m_fastindex);
    Z3_ast result;
    DWORD index;
    Z3_ast reast;
    auto scan = fast_index & fastMask[nbytes << 3];
    if (_BitScanReverse64(&index, scan)) {
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
        scan = fast_index & fastMask[nbytes << 3];
        if (_BitScanReverse64(&index, scan)) {
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
    TRcontext& m_toctx;
    Z3_ast m_ast;
public:
    inline Translate(TRcontext& ctx, TRcontext& toctx, Z3_ast s):
        m_toctx(toctx)
    {
#if !defined(CLOSECNW)&&!defined(USECNWNOAST)
        std::unique_lock<std::mutex> lock(ctx);
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
Z3_ast Reg2Ast(Char nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX& m_ast, TRcontext& ctx, TRcontext& toctx) {
#else
Z3_ast Reg2Ast(Char nbytes, UChar * m_bytes, UChar * m_fastindex, Z3_ast * m_ast, TRcontext & ctx, TRcontext & toctx) {
#endif
    ULong fast_index = GET8(m_fastindex);
    Z3_ast result;
    DWORD index;
    Z3_ast reast;
    auto scan = fast_index & fastMask[nbytes << 3];
    if (_BitScanReverse64(&index, scan)) {
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
        scan = fast_index & fastMask[nbytes << 3];
        if (_BitScanReverse64(&index, scan)) {
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
