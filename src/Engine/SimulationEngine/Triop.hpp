


Vns Kernel::T_Triop(context &m_ctx, IROp op, Vns const&a, Vns const&b, Vns const&c) {
    if (a.symbolic() || b.symbolic() || c.symbolic()) {
        switch (op) {
        case Iop_DivF64: {return Vns(m_ctx, Z3_mk_fpa_div(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<64>()), c.bv2fpa(m_ctx.fpa_sort<64>()))).fpa2bv(); }
        case Iop_MulF64: {return Vns(m_ctx, Z3_mk_fpa_mul(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<64>()), c.bv2fpa(m_ctx.fpa_sort<64>()))).fpa2bv(); }
        case Iop_DivF32: {return Vns(m_ctx, Z3_mk_fpa_div(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<32>()), c.bv2fpa(m_ctx.fpa_sort<32>()))).fpa2bv(); }
        case Iop_MulF32: {return Vns(m_ctx, Z3_mk_fpa_mul(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<32>()), c.bv2fpa(m_ctx.fpa_sort<32>()))).fpa2bv(); }
        default:
        }
    }
    else {
        switch (op) {
        case Iop_DivF64: {return ((Int)(a) == 0) ? Vns(m_ctx, ((double)b) / ((double)c), 64) : Vns(m_ctx, Z3_mk_fpa_div(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<64>()), c.bv2fpa(m_ctx.fpa_sort<64>()))).fpa2bv().simplify(); }
        case Iop_MulF64: {return ((Int)(a) == 0) ? Vns(m_ctx, ((double)b) * ((double)c), 64) : Vns(m_ctx, Z3_mk_fpa_mul(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<64>()), c.bv2fpa(m_ctx.fpa_sort<64>()))).fpa2bv().simplify(); }
        case Iop_DivF32: {return ((Int)(a) == 0) ? Vns(m_ctx, ((float)b) / ((float)c), 32) : Vns(m_ctx, Z3_mk_fpa_div(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<32>()), c.bv2fpa(m_ctx.fpa_sort<32>()))).fpa2bv().simplify(); }
        case Iop_MulF32: {return ((Int)(a) == 0) ? Vns(m_ctx, ((float)b) * ((float)c), 32) : Vns(m_ctx, Z3_mk_fpa_mul(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<32>()), c.bv2fpa(m_ctx.fpa_sort<32>()))).fpa2bv().simplify(); }
        default:
        }
    }
FAILD:
    vex_printf("unsupport Triop: ");
    ppIROp(op);
    vpanic("tIRType");
}