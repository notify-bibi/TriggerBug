


inline Variable State::T_Triop(IROp op, IRExpr* arg1, IRExpr* arg2, IRExpr* arg3) {
	Variable a = tIRExpr(arg1);
	Variable b = tIRExpr(arg2);
	Variable c = tIRExpr(arg3);
	if (a.symbolic() || b.symbolic() || c.symbolic()) goto dosymbol;
	switch (op) {
	case Iop_DivF64: {return ((Int)(a) == 0) ? Variable(((double)b) / ((double)c), a, 64) : Variable(m_ctx, Z3_mk_fpa_div(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<64>()), c.bv2fpa(m_ctx.fpa_sort<64>()))).fpa2bv().simplify(); }
	case Iop_MulF64: {return ((Int)(a) == 0) ? Variable(((double)b) * ((double)c), a, 64) : Variable(m_ctx, Z3_mk_fpa_mul(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<64>()), c.bv2fpa(m_ctx.fpa_sort<64>()))).fpa2bv().simplify(); }
	case Iop_DivF32: {return ((Int)(a) == 0) ? Variable(((float)b) / ((float)c), a, 32) : Variable(m_ctx, Z3_mk_fpa_div(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<32>()), c.bv2fpa(m_ctx.fpa_sort<32>()))).fpa2bv().simplify(); }
	case Iop_MulF32: {return ((Int)(a) == 0) ? Variable(((float)b) * ((float)c), a, 32) : Variable(m_ctx, Z3_mk_fpa_mul(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<32>()), c.bv2fpa(m_ctx.fpa_sort<32>()))).fpa2bv().simplify(); }
	default:
		ppIROp(op);
		vpanic("memcheck:expr2vbits_Triop");
	}

dosymbol:
	switch (op) {
	case Iop_DivF64: {return Variable(m_ctx, Z3_mk_fpa_div(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<64>()), c.bv2fpa(m_ctx.fpa_sort<64>()))).fpa2bv(); }
	case Iop_MulF64: {return Variable(m_ctx, Z3_mk_fpa_mul(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<64>()), c.bv2fpa(m_ctx.fpa_sort<64>()))).fpa2bv(); }
	case Iop_DivF32: {return Variable(m_ctx, Z3_mk_fpa_div(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<32>()), c.bv2fpa(m_ctx.fpa_sort<32>()))).fpa2bv(); }
	case Iop_MulF32: {return Variable(m_ctx, Z3_mk_fpa_mul(m_ctx, translateRM(m_ctx, a), b.bv2fpa(m_ctx.fpa_sort<32>()), c.bv2fpa(m_ctx.fpa_sort<32>()))).fpa2bv(); }
	default:
		ppIROp(op);
		vpanic("memcheck:expr2vbits_Triop");
	}
}