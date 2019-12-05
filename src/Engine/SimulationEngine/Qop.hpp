inline Vns State::T_Qop(context &m_ctx, IROp op, Vns const& a, Vns const& b, Vns const& c, Vns const& d){
    if (a.symbolic() || b.symbolic() || c.symbolic() || d.symbolic()) {
        switch (op) {
        case Iop_64x4toV256: {
            vassert(a.bitn == 64); vassert(b.bitn == 64);
            vassert(c.bitn == 64); vassert(d.bitn == 64);
            return d.Concat(c.Concat(b.Concat(a)));
        }
        case Iop_MAddF64:
        case Iop_MAddF64r32:
        case Iop_MSubF64:
        case Iop_MSubF64r32:
        case Iop_MAddF32:
        case Iop_MSubF32:
        }
    }
    else {
        switch (op) {
        case Iop_64x4toV256: {
            vassert(a.bitn == 64); vassert(b.bitn == 64);
            vassert(c.bitn == 64); vassert(d.bitn == 64);
            return Vns(m_ctx, _mm256_setr_epi64x(a, b, c, d));
        }
        case Iop_MAddF64:
        case Iop_MAddF64r32:
        case Iop_MSubF64:
        case Iop_MSubF64r32:
        case Iop_MAddF32:
        case Iop_MSubF32:

        }
    }
FAILD:
    vex_printf("unsupport Qop: ");
    ppIROp(op);
    vpanic("tIRType");

}