#include "engine/basic_var.hpp"


namespace sv {
    symbol::symbol(Z3_context ctx, uint64_t v, unsigned nbits)
        : m_ctx((_CTX_)ctx)
    {
        Z3_sort zsort = Z3_mk_bv_sort(ctx, nbits);
        Z3_inc_ref((Z3_context)m_ctx, reinterpret_cast<Z3_ast>(zsort));
        m_ast = (_AST_)Z3_mk_unsigned_int64(ctx, v, zsort);
        Z3_inc_ref(ctx, (Z3_ast)m_ast);
        Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
    }

    symbol::symbol(Z3_context ctx, int64_t v, unsigned nbits)
        : m_ctx((_CTX_)ctx)
    {
        Z3_sort zsort = Z3_mk_bv_sort(ctx, nbits);
        Z3_inc_ref((Z3_context)m_ctx, reinterpret_cast<Z3_ast>(zsort));
        m_ast = (_AST_)Z3_mk_int64(ctx, v, zsort);
        Z3_inc_ref(ctx, (Z3_ast)m_ast);
        Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
    }




    static inline Z3_ast _mk_ast_(Z3_context ctx, uint64_t v, unsigned nb)
    {
        sort zsort = bv_sort(ctx, nb);
        Z3_ast r = Z3_mk_unsigned_int64(ctx, v, zsort);
        Z3_inc_ref(ctx, r);
        return r;
    }

    Z3_ast symbol::_mk_ast(Z3_context ctx, const uint64_t* v, unsigned nbit)
    {
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

    void symbol::_simpify() const
    {
        Z3_ast simp = Z3_simplify((Z3_context)m_ctx, (Z3_ast)m_ast);
        Z3_inc_ref((Z3_context)m_ctx, simp);
        Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
        const_cast<symbol*>(this)->m_ast = (_AST_)simp;
    }

    void symbol::_to_fp(const sort& fpa_sort)
    {
        Z3_ast fpa = Z3_mk_fpa_to_fp_bv((Z3_context)m_ctx, (Z3_ast)m_ast, fpa_sort);
        Z3_inc_ref((Z3_context)m_ctx, fpa);
        Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
        m_ast = (_AST_)fpa;
        _simpify();
    }

    sort fpRM(Z3_context ctx, IRRoundingMode md)
    {
        switch (md) {
        case Irrm_NEAREST: { return sort(ctx, Z3_mk_fpa_rne(ctx)); }
        case Irrm_PosINF: { return sort(ctx, Z3_mk_fpa_rtp(ctx)); }
        case Irrm_ZERO: { return sort(ctx, Z3_mk_fpa_rtz(ctx)); }
        case Irrm_NEAREST_TIE_AWAY_0: { return sort(ctx, Z3_mk_fpa_rna(ctx)); }
        case Irrm_NegINF: { return sort(ctx, Z3_mk_fpa_rtn(ctx)); }
        default: VPANIC("NOT SUPPPORT"); return *(sort*)(nullptr);
        }
    }
    std::string tval::str() const
    {
        if (real()) {
            std::string str;
            char buff[0x80];

            if (m_bits <= 64) {
                snprintf(buff, sizeof(buff), "tval %d( 0x%llx )", m_bits, (*(uint64_t*)m_data) & fastMask(m_bits)); goto ret;
            }
            if (m_bits <= 128) {
                snprintf(buff, sizeof(buff), "tval %d( %016llx-%016llx )", m_bits, m_data[1], m_data[0]); goto ret;
            }
            if (m_bits <= 256) {
                snprintf(buff, sizeof(buff), "tval %d( %016llx-%016llx-%016llx-%016llx )", m_bits, m_data[3], m_data[2], m_data[1], m_data[0]);  goto ret;
            }

        ret:
            str.assign(buff);
            return str;
        }
        else {
            std::string str;
            char buff[0x80];
#if 0
            std::string strContent;
            snprintf(buff, sizeof(buff), " BS%d < ", m_bits);
            strContent.assign(buff);
            str.append(strContent);
            strContent.assign(Z3_ast_to_string((Z3_context)m_ctx, m_ast));
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
    tval tval::extract(int hi, int lo) const {
        UShort size = hi - lo + 1;
        if (symb())
            return tval((Z3_context)m_ctx, Z3_mk_extract((Z3_context)m_ctx, hi, lo, (Z3_ast)m_ast), size);

        if (lo < 64 && hi < 64)
            return tval((Z3_context)m_ctx, m_data[0] >> lo, (hi - lo + 1));

        __m256i m32 = *(__m256i*)(&((char*)m_data)[lo >> 3]);
        if (lo & 7) {
            UChar _n = size >> 6;
            UChar _s = (64 - (lo & 7));
            for (int i = 0; i <= _n; i++) {
                m32.m256i_u64[i] = (m32.m256i_u64[i] >> (lo & 7)) | (m32.m256i_u64[i + 1] << _s);
            }
        }
        return tval((Z3_context)m_ctx, m32, size);
    }

    tval tval::concat(tval const& low) const
    {
        assert((low.m_bits + m_bits) <= 256);
        if (!low.m_bits) return *this;
        if (!m_bits) return low;
        if (real() && low.real()) {
            if (low.m_bits & 7) {
                __m256i m32 = *(__m256i*)low.m_data;
                auto base = ((low.m_bits - 1) >> 6);
                m32.m256i_u64[base] &= fastMask(low.m_bits & 63);
                auto shln = low.m_bits & 63;
                auto shrn = (64 - shln);
                m32.m256i_u64[base] |= m_data[0] << shln;
                for (int i = 1; i <= ((m_bits - 1) >> 6); i++) {
                    m32.m256i_u64[base + i] = (m_data[i] << shln) | (m_data[i - 1] >> shrn);
                }
                return tval((Z3_context)m_ctx, m32, low.m_bits + m_bits);
            }
            else {
                __m256i re = *(__m256i*)low.m_data;
                memcpy(&re.m256i_u8[(low.m_bits >> 3)], m_data, (this->m_bits) >> 3);
                return tval((Z3_context)m_ctx, re, low.m_bits + m_bits);
            }
        }
        else {
            return tval((Z3_context)m_ctx, Z3_mk_concat((Z3_context)m_ctx, (Z3_ast)m_ast, low.mk_bv_ast()), low.m_bits + m_bits);
        }
    }
    tval tval::shl(int shn) const
    {
        vassert(shn < 256);
        if (real()) {
            if (m_bits > 64) {
                if (shn & 7) {
                    __m256i m32 = _mm256_set1_epi64x(0ull);
                    auto base = (((UInt)shn - 1) >> 6);
                    m32.m256i_u64[base] &= fastMask((UInt)shn & 63);
                    auto shln = (UInt)shn & 63;
                    auto shrn = (64 - shln);
                    m32.m256i_u64[base] |= m_data[0] << shln;
                    for (int i = 1; i <= ((m_bits - 1) >> 6); i++) {
                        m32.m256i_u64[base + i] = (m_data[i] << shln) | (m_data[i - 1] >> shrn);
                    }
                    return tval((Z3_context)m_ctx, m32, m_bits);
                }
                else {
                    __m256i re = _mm256_set1_epi64x(0ull);;
                    memcpy(&re.m256i_u8[((UInt)shn >> 3)], &this->m_data, (this->m_bits) >> 3);
                    return tval((Z3_context)m_ctx, re, m_bits);
                }
            }
            else {
                return tval((Z3_context)m_ctx, m_data[0] << (UInt)shn, m_bits);
            }
        }
        else {
            return tval((Z3_context)m_ctx, Z3_mk_bvshl((Z3_context)m_ctx, *this, tval((Z3_context)m_ctx, shn, m_bits)), m_bits);
        }
    }
    tval tval::lshr(int shn) const
    {
        vassert(shn < 256);
        if (real()) {
            if (m_bits > 64) {
                return extract(m_bits - 1, shn).zext(shn);
            }
            else {
                return tval((Z3_context)m_ctx, (m_data[0] & fastMask(m_bits)) >> (UInt)shn, m_bits);
            }
        }
        else {
            return tval((Z3_context)m_ctx, Z3_mk_bvlshr((Z3_context)m_ctx, *this, tval((Z3_context)m_ctx, shn, m_bits)), m_bits);
        }
    }

    tval tval::ashr(int shn) const
    {
        vassert(shn < 256);
        if (real()) {
            return extract(m_bits - 1, shn).sext(shn);
        }
        else {
            return tval((Z3_context)m_ctx, Z3_mk_bvashr((Z3_context)m_ctx, *this, tval((Z3_context)m_ctx, shn, m_bits)), m_bits);
        }
    }
    tval tval::zext(int i) const
    {

        if (i < 0)
            return extract(m_bits + i - 1, 0);
        if (symb()) {
            return tval((Z3_context)m_ctx, Z3_mk_zero_ext((Z3_context)m_ctx, i, (Z3_ast)m_ast), m_bits + i);
        }
        auto m32 = *(__m256i*)(m_data);
        if (m_bits & 7) {
            m32.m256i_i8[(m_bits - 1) >> 3] &= fastMask(m_bits & 7);
        }
        memset(&m32.m256i_i8[((m_bits - 1) >> 3) + 1], 0ul, i >> 3);
        return tval((Z3_context)m_ctx, m32, m_bits + i);
    }
    tval tval::sext(int i) const
    {
        if (i < 0)
            return extract(m_bits + i - 1, 0);
        if (symb()) {
            return tval((Z3_context)m_ctx, Z3_mk_sign_ext((Z3_context)m_ctx, i, (Z3_ast)m_ast), m_bits + i);
        }
        auto m32 = *(__m256i*)(&this->m_data);
        if ((((uint8_t*)m_data)[(m_bits - 1) >> 3] >> ((m_bits - 1) & 7)) & 1) {
            if (m_bits & 7) {
                m32.m256i_i8[(m_bits - 1) >> 3] |= fastMaskReverse((m_bits & 7));
            }
            memset(&m32.m256i_i8[((m_bits - 1) >> 3) + 1], -1ul, i >> 3);
        }
        else {
            if (m_bits & 7) {
                m32.m256i_i8[(m_bits - 1) >> 3] &= fastMask(8 - (m_bits & 7));
            }
            memset(&m32.m256i_i8[((m_bits - 1) >> 3) + 1], 0ul, i >> 3);
        }
        return tval((Z3_context)m_ctx, m32, m_bits + i);
    }
    Z3_ast tval::mk_bv_ast() const
    {
        if (m_data_inuse && !m_ast) {
            const_cast<tval*>(this)->m_ast = (_AST_)_mk_ast((Z3_context)m_ctx, (uint64_t*)&m_data, m_bits);
            const_cast<tval*>(this)->m_sk = (_CTX_)Z3_BV_SORT;
            return (Z3_ast)m_ast;
        };
        if (m_sk == Z3_BV_SORT) {
            return (Z3_ast)m_ast;
        }
        return (Z3_ast)-1;

    }
};


//static Z3_ast bool2bv(Z3_context ctx, Z3_ast ast) {
//    Z3_inc_ref(ctx, ast);
//    Z3_sort sort = Z3_mk_bv_sort(ctx, 1);
//    Z3_inc_ref(ctx, (Z3_ast)sort);
//    Z3_ast zero = Z3_mk_int(ctx, 0, sort);
//    Z3_inc_ref(ctx, zero);
//    Z3_ast one = Z3_mk_int(ctx, 1, sort);
//    Z3_inc_ref(ctx, one);
//    Z3_ast result = Z3_mk_ite(ctx, ast, one, zero);
//    Z3_dec_ref(ctx, one);
//    Z3_dec_ref(ctx, zero);
//    Z3_dec_ref(ctx, ast);
//    Z3_dec_ref(ctx, (Z3_ast)sort);
//    return result;
//}

//inline Z3_ast mk_bool_ast() const {
//    vassert(m_bits == 1);
//    if (m_data_inuse && !m_ast) {
//        const_cast<tval*>(this)->m_ast = (_AST_)(((*(int*)m_data) & 1) ? Z3_mk_true((Z3_context)m_ctx) : Z3_mk_false((Z3_context)m_ctx));
//        const_cast<tval*>(this)->m_sk = (_CTX_)Z3_BOOL_SORT;
//        return (Z3_ast)m_ast;
//    }
//    if (m_sk == Z3_BOOL_SORT) {
//        return (Z3_ast)m_ast;
//    }
//    if (m_sk == Z3_BV_SORT) {
//        Z3_sort sort = Z3_mk_bv_sort((Z3_context)m_ctx, 1);
//        Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)sort);
//        Z3_ast one = Z3_mk_int((Z3_context)m_ctx, 1, sort);
//        Z3_inc_ref((Z3_context)m_ctx, one);
//        Z3_ast b = Z3_mk_eq((Z3_context)m_ctx, (Z3_ast)m_ast, one);
//        Z3_inc_ref((Z3_context)m_ctx, b);
//        Z3_dec_ref((Z3_context)m_ctx, one);
//        Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)sort);
//        Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
//        const_cast<tval*>(this)->m_ast = (_AST_)b;
//        const_cast<tval*>(this)->m_sk = (_CTX_)Z3_BOOL_SORT;
//        return b;
//    }
//    return (Z3_ast)-1;
//}
//template<unsigned ebits, unsigned sbits>
//inline Z3_ast mk_fpa_ast() const {
//    static_assert(ebits > 0 && sbits > 0 && (sbits + ebits <= 256), "gg size");
//    vassert(ebits + sbits == m_bits);
//    if (m_data_inuse && !m_ast) {
//        const_cast<tval*>(this)->m_ast = (_AST_)_mk_ast((Z3_context)m_ctx, (uint64_t*)&m_data, m_bits);
//        sort s = sv::fpa_sort((Z3_context)m_ctx, ebits, sbits);
//        Z3_ast fpa = Z3_mk_fpa_to_fp_bv((Z3_context)m_ctx, (Z3_ast)m_ast, s);
//        Z3_inc_ref((Z3_context)m_ctx, fpa);
//        Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
//        const_cast<tval*>(this)->m_ast = (_AST_)fpa;
//        _simpify();
//        const_cast<tval*>(this)->m_sk = (_CTX_)Z3_FLOATING_POINT_SORT;
//        return fpa;
//    }
//    if (m_sk == Z3_FLOATING_POINT_SORT) {
//        return (Z3_ast)m_ast;
//    }
//    if (m_sk == Z3_BV_SORT) {
//        sort s = sv::fpa_sort((Z3_context)m_ctx, ebits, sbits);
//        Z3_ast fpa = Z3_mk_fpa_to_fp_bv((Z3_context)m_ctx, (Z3_ast)m_ast, s);
//        Z3_inc_ref((Z3_context)m_ctx, fpa);
//        Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
//        const_cast<tval*>(this)->m_sk = (_CTX_)Z3_FLOATING_POINT_SORT;
//        const_cast<tval*>(this)->m_ast = (_AST_)fpa;
//        return fpa;
//    }
//    return (Z3_ast)-1;
//}

void HexToStr(unsigned char* pbDest, unsigned char* pbSrc, int nLen)

{
    char ddl, ddh;
    int i;
    pbDest[nLen * 2] = '\0';
    nLen--;
    for (i = 0; i <= nLen; i++)
    {
        ddh = 48 + pbSrc[i] / 16;
        ddl = 48 + pbSrc[i] % 16;
        if (ddh > 57) ddh = ddh + 7;
        if (ddl > 57) ddl = ddl + 7;
        ((short*)pbDest)[(nLen - i)] = ((short)ddl << 8) | ddh;
    }
};
