#include "crypto_analyzer/ana_des.h"
using namespace z3;

expr ana_des::item(expr const& exp, Int base)
{
    context& ctx = exp.ctx();
    expr r = ctx.bv_val(0x63, 8);

    for (int i = 1; i < 256; i++) {
        expr d = exp == (base + i * 4);
        r = ite(d, ctx.bv_val(des_se[i], 8), r);
    }
    return r;
}


static Z3_ast ana_des::dword_4062E0(Addr64, Z3_ast maddr) {
    expr s = item(expr(m_ctx, maddr), 0x4062E0);
    expr r = concat(concat(concat((s), (s)), xtime3(s)), xtime(s));
    Z3_inc_ref(m_ctx, r);
    return r;
}

static Z3_ast ana_des::dword_4059E0(Addr64, Z3_ast maddr) {
    expr s = item(expr(m_ctx, maddr), 0x4059E0);
    expr r = concat(concat(concat(xtime(s), (s)), (s)), xtime3(s));
    Z3_inc_ref(m_ctx, r);
    return r;
}

static Z3_ast ana_des::dword_4055E0(Addr64, Z3_ast maddr) {
    expr s = item(expr(m_ctx, maddr), 0x4055E0);
    expr r = concat(concat(concat(xtime3(s), xtime(s)), (s)), (s));
    Z3_inc_ref(m_ctx, r);
    return r;
}

static Z3_ast ana_des::dword_4051E0(Addr64, Z3_ast maddr) {
    expr s = item(expr(m_ctx, maddr), 0x4051E0);
    expr r = concat(concat(concat((s), xtime3(s)), xtime(s)), (s));
    Z3_inc_ref(m_ctx, r);
    return r;
}

bool ana_des::check()
{
    


    return false;
}
