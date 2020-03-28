#include "engine/op_header.h"


tval Kernel::tQop(IROp op, tval const& a, tval const& b, tval const& c, tval const& d){
    if (a.symb() || b.symb() || c.symb() || d.symb()) {
        switch (op) {
        case Iop_64x4toV256: { return dtos(64).concat(ctos(64).concat(btos(64).concat(atos(64)))); }
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
        case Iop_64x4toV256: { return tval(a, _mm256_setr_epi64x(ato(int64_t), bto(int64_t), cto(int64_t), dto(int64_t))); }
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