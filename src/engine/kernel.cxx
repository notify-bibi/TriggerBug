#include "kernel.h"
#include "state_class.h"

using namespace TR;


z3::sort translateRM(z3::context& m_ctx, IRRoundingMode md) {
    switch (md)
    {
    case Irrm_NEAREST: {return z3::sort(m_ctx, Z3_mk_fpa_rne(m_ctx)); }
    case Irrm_PosINF: {return z3::sort(m_ctx, Z3_mk_fpa_rtp(m_ctx)); }
    case Irrm_ZERO: {return z3::sort(m_ctx, Z3_mk_fpa_rtz(m_ctx)); }
    case Irrm_NEAREST_TIE_AWAY_0: {return z3::sort(m_ctx, Z3_mk_fpa_rna(m_ctx)); }
    default:
        vassert(md == Irrm_NegINF);
        return z3::sort(m_ctx, Z3_mk_fpa_rtn(m_ctx));
    }
}


