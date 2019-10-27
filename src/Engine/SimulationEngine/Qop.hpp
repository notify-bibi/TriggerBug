inline Vns State::T_Qop(IROp op, IRExpr* arg1, IRExpr* arg2, IRExpr* arg3, IRExpr* arg4){
	Vns a = tIRExpr(arg1);
	Vns b = tIRExpr(arg2);
	Vns c = tIRExpr(arg3);
	Vns d = tIRExpr(arg4);
	if (a.symbolic() || b.symbolic() || c.symbolic()|| d.symbolic()) goto dosymbol;
	switch (op) {
	case Iop_MAddF64:
	case Iop_MAddF64r32:
	case Iop_MSubF64:
	case Iop_MSubF64r32:
		/* I32(rm) x F64 x F64 x F64 -> F64 */
		//return mkLazy4(mce, Ity_I64, vatom1, vatom2, vatom3, vatom4);

	case Iop_MAddF32:
	case Iop_MSubF32:
		/* I32(rm) x F32 x F32 x F32 -> F32 */
		//return mkLazy4(mce, Ity_I32, vatom1, vatom2, vatom3, vatom4);

		/* V256-bit data-steering */
	case Iop_64x4toV256: {
		vassert(a.bitn == 64); vassert(b.bitn == 64);
		vassert(c.bitn == 64); vassert(d.bitn == 64); 
		return Vns(m_ctx, _mm256_setr_epi64x(a, b, c, d));
	}
		//return assignNew('V', mce, Ity_V256,IRExpr_Qop(op, vatom1, vatom2, vatom3, vatom4));
		
	default:
		ppIROp(op);
		vpanic("expr2vbits_Qop");
	}
dosymbol:
	switch (op) {
	case Iop_MAddF64:
	case Iop_MAddF64r32:
	case Iop_MSubF64:
	case Iop_MSubF64r32:
		/* I32(rm) x F64 x F64 x F64 -> F64 */
		//return mkLazy4(mce, Ity_I64, vatom1, vatom2, vatom3, vatom4);

	case Iop_MAddF32:
	case Iop_MSubF32:
		/* I32(rm) x F32 x F32 x F32 -> F32 */
		//return mkLazy4(mce, Ity_I32, vatom1, vatom2, vatom3, vatom4);

		/* V256-bit data-steering */
	case Iop_64x4toV256: 
		

	default:
		ppIROp(op);
		vpanic("expr2vbits_Qop");
	}
}