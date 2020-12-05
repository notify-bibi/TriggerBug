#include "engine/op_header.h"
/* ---------------------------------------------------------------------------------------
 *      Notify-bibi Symbolic-Emulation-Engine project
 *      Copyright (c) 2019 Microsoft Corporation by notify-bibi@github, 2496424084@qq.com
 *      ALL RIGHTS RESERVED.
 *
 *      快速地执行 IR operator 并返回
 *      如果是你需要的op code，请帮我完善还未能实现的 IR op
 * ---------------------------------------------------------------------------------------
 */


tval Kernel::tTriop(IROp op, tval const&a, tval const&b, tval const&c) {
    if (a.symb() || b.symb() || c.symb()) {
        switch (op) {
        case Iop_DivF64: {
            sv::sort rm = sv::fpRM(a, atorm);
            return ((sfpval<64>&)b).div(rm, ((sfpval<64>&)c));
        }
        case Iop_MulF64: {
            sv::sort rm = sv::fpRM(a, atorm);
            return ((sfpval<64>&)b).mul(rm, ((sfpval<64>&)c));
        }
        case Iop_DivF32: {
            sv::sort rm = sv::fpRM(a, atorm);
            return ((sfpval<32>&)b).div(rm, ((sfpval<32>&)c));
        }
        case Iop_MulF32: {
            sv::sort rm = sv::fpRM(a, atorm);
            return ((sfpval<32>&)b).mul(rm, ((sfpval<32>&)c));
        }
        default:
        }
    }
    else {
        switch (op) {
        case Iop_DivF64: { 
            if ((Int)(ato(int)) == 0) return (bto(double) / cto(double));
            return ((sfpval<64>&)b).div(sv::fpRM(a, atorm), ((sfpval<64>&)c)).simplify();
        }
        case Iop_MulF64: { 
            if ((Int)(ato(int)) == 0) return (bto(double) * cto(double));
            return ((sfpval<64>&)b).mul(sv::fpRM(a, atorm), ((sfpval<64>&)c)).simplify();
        }
        case Iop_DivF32: {
            if ((Int)(ato(int)) == 0) return (bto(float) / cto(float));
            return ((sfpval<32>&)b).div(sv::fpRM(a, atorm), ((sfpval<32>&)c)).simplify();
        }
        case Iop_MulF32: { 
            if ((Int)(ato(int)) == 0) return (bto(float) * cto(float));
            return ((sfpval<32>&)b).mul(sv::fpRM(a, atorm), ((sfpval<32>&)c)).simplify();
        }
        default:
        }
    }
FAILD:
    vex_printf("unsupport Triop: ");
    ppIROp(op);
    vpanic("tIRType");
}