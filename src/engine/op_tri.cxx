#include "engine/op_header.h"

//
//tval Kernel::tTriop(IROp op, tval const&a, tval const&b, tval const&c) {
//    if (a.symb() || b.symb() || c.symb()) {
//        switch (op) {
//        case Iop_DivF64: {
//            sv::sort rm = sv::fpRM(a, (IRRoundingMode)(int)(cInt&)a);
//            return ((fpval<64>&)b).div(rm, ((fpval<64>&)c));
//        }
//        case Iop_MulF64: {
//            sv::sort rm = sv::fpRM(a, (IRRoundingMode)(int)(cInt&)a);
//            return ((fpval<64>&)b).mul(rm, ((fpval<64>&)c));
//        }
//        case Iop_DivF32: {
//            sv::sort rm = sv::fpRM(a, (IRRoundingMode)(int)(cInt&)a);
//            return ((fpval<32>&)b).div(rm, ((fpval<32>&)c));
//        }
//        case Iop_MulF32: {
//            sv::sort rm = sv::fpRM(a, (IRRoundingMode)(int)(cInt&)a);
//            return ((fpval<32>&)b).mul(rm, ((fpval<32>&)c));
//        }
//        default:
//        }
//    }
//    else {
//        switch (op) {
//        case Iop_DivF64: { 
//            if ((Int)(ato(int)) == 0) return (bto(double) / cto(double));
//            return ((fpval<64>&)b).div(sv::fpRM(a, (IRRoundingMode)(int)(cInt&)a), ((fpval<64>&)c)).simplify();
//        }
//        case Iop_MulF64: { 
//            if ((Int)(ato(int)) == 0) return (bto(double) * cto(double));
//            return ((fpval<64>&)b).mul(sv::fpRM(a, (IRRoundingMode)(int)(cInt&)a), ((fpval<64>&)c)).simplify();
//        }
//        case Iop_DivF32: {
//            if ((Int)(ato(int)) == 0) return (bto(float) / cto(float));
//            return ((fpval<32>&)b).div(sv::fpRM(a, (IRRoundingMode)(int)(cInt&)a), ((fpval<32>&)c)).simplify();
//        }
//        case Iop_MulF32: { 
//            if ((Int)(ato(int)) == 0) return (bto(float) * cto(float));
//            return ((fpval<32>&)b).mul(sv::fpRM(a, (IRRoundingMode)(int)(cInt&)a), ((fpval<32>&)c)).simplify();
//        }
//        default:
//        }
//    }
//FAILD:
//    vex_printf("unsupport Triop: ");
//    ppIROp(op);
//    vpanic("tIRType");
//}