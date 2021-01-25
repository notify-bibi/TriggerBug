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


tval TR::StateBase::tQop(IROp op, tval const& a, tval const& b, tval const& c, tval const& d){
    if (a.symb() || b.symb() || c.symb() || d.symb()) {
        switch (op) {
        case Iop_64x4toV256: { return dtos(64).concat(ctos(64).concat(btos(64).concat(atos(64)))); }
        case Iop_MAddF64:
        case Iop_MAddF64r32:
        case Iop_MSubF64:
        case Iop_MSubF64r32:
        case Iop_MAddF32:
        case Iop_MSubF32:
        default:
            break;
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
        default:
            break;
        }
    }
FAILD:
    vex_printf("unsupport Qop: ");
    ppIROp(op);
    vpanic("tIRType");

}