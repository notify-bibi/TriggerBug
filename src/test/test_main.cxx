
#include "test.h"
#include "engine/basic_var.hpp"
#include <Windows.h>


using namespace TR;


//using Vns = sv::tval;

#define cbool_assert(expr) if UNLIKELY(!(expr)) return false;

bool test_basic_var_real() {
    z3::context c;
    
    
    cbool bo1(c, false);
    cbool bo2(c, true);
    
    cbool_assert(bo1 ^ bo2);
    cbool_assert(bo1 || bo2);
    cbool_assert(!(bo1 && bo2));

    rcval<uint16_t>  uint16(c, 0xffff);
    rcval<int16_t>  int16(c, 0xffff);
    rcval<int32_t>  int32(c, -1);
    rcval<uint32_t>  uint32(c, -1);

    cbool_assert(uint16 == 0xffff);
    cbool_assert(int16 == -1);
    cbool_assert(int32 == -1);
    cbool_assert(uint32 == 0xffffffff);


    sv::ctype_val< true, 48, Z3_BV_SORT> int48(c, 1ll << 47);
    sv::ctype_val< false, 48, Z3_BV_SORT> uint48(c, 1ll << 47);
    cbool_assert(int48 == -(1ll << 47));
    cbool_assert(uint48 == (1ll << 47));
    rcval<__m128i>  m128(c, _mm_set1_epi8(9));

    //cbool_assert((m128.extract<127, 120>()) == 9);
    sv::ctype_val<false, 128, Z3_BV_SORT>  m128a(c, 9);
    sv::ctype_val<false, 256, Z3_BV_SORT>  m128b(c, 9);
    sv::ctype_val<true, 256, Z3_BV_SORT>  m256d(c, -999);
    sv::ctype_val<false, 78, Z3_BV_SORT>  m128c(c, -9);

    int kk1 = m128c;
    int kk2 = m256d;
    cbool_assert(kk1 == -9);
    cbool_assert(kk2 == -999);

    sv::ctype_val<true, 63, Z3_BV_SORT>  sm78(c, -1);
    sv::ctype_val<false, 63, Z3_BV_SORT>  um78(c, -1);

    rcval<__m256i>  m256(c, _mm256_set_epi64x(9, 6, 3, 1));



    __m128i i128 = m128;


    cbool_assert(( int48 >> 8) == (-(1ll << 47))/0b100000000);
    cbool_assert((uint48 >> 8) == 0x008000000000);
    cbool_assert(int48 < 0);
    cbool_assert(uint48 > 0);



    cbool_assert(int16 < 8);
    cbool_assert(uint32 + 8989 == 0x000231C);
    cbool_assert(uint32 - 89 == 0xFFFFFFA6);



    return true;
}




bool test_basic_var_sym() {
    z3::context c;
    sv::symbolic<true, 32, Z3_BV_SORT > s32t(c, -5);
    sv::symbolic<true, 16, Z3_BV_SORT > s16t(c, -5);

    rsval<int>  hjk1(c, 8);
    rsval<int>  hjk2(c, 8);
    rsval<int>  sss1(s32t);
    rsval<short>  sss2(s16t);
    rsval<bool>  bo1(c, false);
    rsval<bool>  bo2(c, true);

    sv::rsval<true, 128, Z3_BV_SORT > s128t(c, _mm_setr_epi32(1, 2, 3, 4));
    //sv::rsval<true, 128, Z3_FLOATING_POINT_SORT> fff128 = s128t;

    __m128i m = s128t.tos().simplify().tor();
    int bb128 = _mm_movemask_epi8(_mm_cmpeq_epi64(_mm_setr_epi32(1, 2, 3, 4), m));
    cbool_assert(0xffff == bb128);
    std::cout << hjk1 + hjk2 << std::endl;
    std::cout << hjk1 + sss1 << std::endl;
    std::cout << hjk1.tos() << sss2 << std::endl;
    std::cout << hjk1 + sss2 + -1ull << std::endl;


    std::cout << hjk1 + 45 - 67 / 54 * 66 + sss2 + -1ull << std::endl;

    std::cout << (hjk1 + sss2 << 56u) << std::endl;
    std::cout << ((((((sss2 + hjk1 >> 5u)) * 5 % 8 | 90) & 56ll) > 8989) && bo1 || bo2) << std::endl;

    std::cout << sss2.concat(hjk1) << std::endl;
    std::cout << sss2.extract<8, 6>() << std::endl;
    std::cout << hjk1.extract<7, 2>() << std::endl;





    //std::cout << (hjk1 + sss2 << 1ull) << std::endl;
    //std::cout << (hjk1 + sss2 >> 1ull) << std::endl;












    sv::symbolic<true, 32, Z3_BV_SORT > d2(c, -5);
    sv::symbolic<false, 32, Z3_BV_SORT > d3(c, -5);



    sv::symbolic<false, 16, Z3_BV_SORT > d4(c, (UShort)-5);

    __m128i sd = _mm_setr_epi32(1, 2, 3, 4);
    sv::symbolic<true, 72, Z3_FLOATING_POINT_SORT > f10_62(c, sd, sv::fpa_sort(c, 10, 62));

    sv::rsval<true, 128, Z3_BV_SORT > jk(c, 89);

    sv::symbolic<false, 16, Z3_FLOATING_POINT_SORT > F16(c, (UShort)0x3f89, sv::fpa_sort(c, 5, 11));

    tval tv4 = F16;

    //sfpval<16>& fa = (sfpval<16>&) tv4;

    //std::cout << fa << std::endl;

    sbool sb(c, false);
    sbool sb2(c, false);

    sv::sort rm = sv::fpRM(c, Irrm_NegINF);
    auto f1 = f10_62.fpa2fpa<5, 6>(rm);
    auto _f1 = f10_62.fpa2fpa<5, 6>(Irrm_NegINF);

    auto x1 = d2 + 8;
    auto x2 = d3 + 8;
    auto x3 = d2 + d3;
    auto x4 = d3 + d2;
    auto x5 = d4 + d2;
    auto x6 = d4 + d3;
    auto x7 = d2 + d4;
    auto x8 = d3 + d4;

    std::cout << f1 << std::endl;
    std::cout << f10_62 << std::endl;
    __m128i mb72 = f10_62.tobv().simplify().tor();
    int bbmb72 = _mm_movemask_epi8(_mm_cmpeq_epi64(_mm_setr_epi32(1, 2, 3, 0), mb72));
    cbool_assert(0xffff == bbmb72);
    std::cout << d2 << std::endl;



    sv::symbolic<false, 240, Z3_BV_SORT > ug240(c, c.bv_const("ug240", 240));
    sv::symbolic<true, 240, Z3_BV_SORT > sg240(c, c.bv_const("sg240", 240));
    sv::symbolic<true, 32, Z3_BV_SORT > sg32(c, c.bv_const("sg32", 32));
    std::cout << ug240 << std::endl;
    std::cout << (sb ^ sb2) << std::endl;

    uint64_t UI64 = 1;
    uint32_t UI32 = 1;
    int64_t I64 = -2;
    uint32_t u32 = 2;
    int32_t I32 = -2;


    auto dd = I64 + UI32;
    auto dd2 = I64 + UI64;

    auto div1 = I64 / u32;//idiv  u32->I64
    auto div2 = UI32 / I64;// idiv  UI32->I64
    auto div3 = UI64 / I32;//div   I32->UI64
    auto div4 = UI32 / UI64;// div 

    auto div5 = UI64 / I64;// div 
    auto div6 = I64 / UI64;// div 



    bool cmp64 = UI64 < I64;//true : ȡ���� UI64
    cmp64 = I32 > UI32;

    cmp64 = UI64 < I32;//true : ȡ���� UI64
    cmp64 = I32 > UI64;

    cmp64 = I64 > UI64;//true
    cmp64 = I64 > UI32;//false




    cmp64 = UI32 < I64;//false : ȡ���� I64
    cmp64 = UI32 < I32;//true : ȡ���� UI32




    std::cout << (ug240 > -1ull) << std::endl;
    std::cout << (ug240 < -1) << std::endl;


    std::cout << (sg32 > -1ull) << std::endl;
    std::cout << (sg32 < -1) << std::endl;
    std::cout << (sg32 < -1ll) << std::endl;

    std::cout << (sg240 > 1ull) << std::endl;
    std::cout << (sg240 > 1) << std::endl;
    std::cout << (sg240 < -1) << std::endl;

    sv::symbolic<true, 233, Z3_BV_SORT > d233(c, c.bv_const("sg233", 233));
    sv::symbolic<false, 233, Z3_BV_SORT > ud233(c, c.bv_const("ug233", 233));
    std::cout << (ug240 >= d233) << std::endl;
    std::cout << (sg240 >= d233) << std::endl;
    std::cout << (sg240 > ud233) << std::endl;


    

    auto v_Iop_Clz32 = Kernel::tUnop(Iop_Clz32, sv::rsval<true, 32, Z3_BV_SORT>(c, 0b1111100)).tors<true, 32, Z3_BV_SORT>();
    auto v_Iop_Ctz32 = Kernel::tUnop(Iop_Ctz32, sv::rsval<true, 32, Z3_BV_SORT>(c, 0b1111100)).tors<true, 32, Z3_BV_SORT>();
    auto v_Iop_Clz64 = Kernel::tUnop(Iop_Clz64, sv::rsval<true, 64, Z3_BV_SORT>(c, 0b1111100)).tors<true, 64, Z3_BV_SORT>();
    auto v_Iop_Ctz64 = Kernel::tUnop(Iop_Ctz64, sv::rsval<true, 64, Z3_BV_SORT>(c, 0b1111100)).tors<true, 64, Z3_BV_SORT>();

    auto s_Iop_Clz32 = Kernel::tUnop(Iop_Clz32, sv::rsval<true, 32, Z3_BV_SORT>(c, 0b1111100).tos()).tos<true, 32, Z3_BV_SORT>().simplify();
    auto s_Iop_Ctz32 = Kernel::tUnop(Iop_Ctz32, sv::rsval<true, 32, Z3_BV_SORT>(c, 0b1111100).tos()).tos<true, 32, Z3_BV_SORT>().simplify();
    auto s_Iop_Clz64 = Kernel::tUnop(Iop_Clz64, sv::rsval<true, 64, Z3_BV_SORT>(c, 0b1111100).tos()).tos<true, 64, Z3_BV_SORT>().simplify();
    auto s_Iop_Ctz64 = Kernel::tUnop(Iop_Ctz64, sv::rsval<true, 64, Z3_BV_SORT>(c, 0b1111100).tos()).tos<true, 64, Z3_BV_SORT>().simplify();
                      
    auto s_Iop_Clz64_O = Kernel::tUnop(Iop_Clz64, sv::rsval<true, 64, Z3_BV_SORT>(c, 1)).tors<true, 64, Z3_BV_SORT>();;
    auto s_Iop_Clz64_0 = Kernel::tUnop(Iop_Clz64, sv::rsval<true, 64, Z3_BV_SORT>(c, 1).tos()).tos<true, 64, Z3_BV_SORT>().simplify();


    cbool_assert((v_Iop_Clz32 == s_Iop_Clz32).tor());
    cbool_assert((v_Iop_Ctz32 == s_Iop_Ctz32).tor());
    cbool_assert((v_Iop_Clz64 == s_Iop_Clz64).tor());
    cbool_assert((v_Iop_Ctz64 == s_Iop_Ctz64).tor());
    cbool_assert((s_Iop_Clz64_O == s_Iop_Clz64_0).tor());

    return true;
    //Z3_inc_ref(sg240, sg240);
}



//
//State_Tag success_ret(Kernel* _s) {
//    vex_printf("success_ret  ??????????\n\n%d");
//    return (State_Tag)0x999;
//
//    s->solv.push();
//    auto ecx = s->regs.Iex_Get<Ity_I32>(12);
//    auto edi = s->regs.Iex_Get<Ity_I32>(36);
//
//    for (int i = 0; i < 44; i++) {
//        auto al = s->mem.Iex_Load<Ity_I8>(ecx + i);
//        auto bl = s->mem.Iex_Load<Ity_I8>(edi + i);
//        s->solv.add(al == bl);
//    }
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("sat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    return Death;
//}
//
//
//State_Tag success_ret2(State* s) {
//
//    s->solv.push();
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("sat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    exit(1);
//    return Death;
//}
//
//


//State_Tag success_ret33(State* s) {
//    s->solv.push();
//    UChar bf[] = { 133, 67, 104, 133, 245, 38, 60, 61, 39, 245, 51, 104, 62, 60, 118, 38, 245, 118, 165, 245, 19, 165, 61, 245, 62, 165, 45, 61, 245, 7, 60, 118, 29, 60, 15, 0, 133, 169 };
//
//    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rax);
//    for (int i = 0; i < 38; i++) {
//        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
//        s->solv.add(e == (UChar)bf[i]);
//    }
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("issat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//        exit(0);
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    return Death;
//}
//
//
//State_Tag whil(State* s) {
//    return (State_Tag)0x233;
//}
//
//State_Tag pp(State* s) {
//    auto al = s->regs.Iex_Get<Ity_I32>(AMD64_IR_OFFSET::eax);
//    std::cout << Z3_ast_to_string(al, al) << std::endl;
//    s->regs.Ist_Put(AMD64_IR_OFFSET::rax, 38ull);
//    s->hook_pass(5);
//    return (State_Tag)Running;
//}
//
//State_Tag Dea(State* s) {
//    return (State_Tag)Death;
//}



#include "engine/guest_layout_helper.h"
//
//Vns flag_limit(Vns& flag) {
//    char flags_char[] = "@_-{}1:() ^";
//    Vns re = Vns(flag, flags_char[0]) == flag;
//    for (int i = 1; i < sizeof(flags_char); i++) {
//        re = re || (Vns(flag, flags_char[i]) == flag);
//    }
//    auto ao1 = flag >= 'a' && flag <= 'z';
//    auto ao2 = flag >= 'A' && flag <= 'Z';
//    auto ao3 = flag >= '0' && flag <= '9';
//    return re || ao1 || ao2 || ao3;
//}
//

State_Tag test_ir_dirty_hook(State<Addr32>& state) {
    UInt esp = 0x8000 - 532;
    PWOW64_CONTEXT ContextRecord = (PWOW64_CONTEXT)(esp - sizeof(WOW64_CONTEXT));
    PEXCEPTION_RECORD32 ExceptionRecord = (PEXCEPTION_RECORD32)(esp - sizeof(WOW64_CONTEXT) - sizeof(EXCEPTION_RECORD32));
    
    if ((Addr32) state.vex_stack_get(1).tor() != (Addr32)(ULong)ContextRecord) return Death;
    if ((UInt)state.vex_stack_get(2).tor() != EXCEPTION_BREAKPOINT) return Death;
    if ((UInt)state.vex_stack_get(22 + offsetof(WOW64_CONTEXT, Esp) / 4).tor() != 0x8000) return Death;
    return Exit;
}

bool test_ir_dirty() {
    ctx32 v(VexArchX86, "");
    v.set_system(windows);
    v.param().set("ntdll_KiUserExceptionDispatcher", 0x2000);

    SP::win32 state(v, 0, True);
    state.setFlag(CF_traceJmp);
    state.setFlag(CF_ppStmts);
    state.mem.map(0x1000, 0x2000);
    state.mem.map(0x5000, 0x5000);
    state.hook_add(0x2000, test_ir_dirty_hook);
    state.mem.store(0x1000, 0xcc);

    state.regs.set(X86_IR_OFFSET::ESP, 0x8000);
    state.regs.set(X86_IR_OFFSET::EIP, 0x1000);
    state.regs.set(X86_IR_OFFSET::CC_OP, 0x0);


    state.start(0x1000);

    return state.status() == Exit;
}




bool creakme();
bool asong();


bool test_cmpress() {
    ctx64 v(VexArchAMD64, "");
    SP::linux64 state(v, 0, True);

    state.mem.map(0x602000, 0x2000);
    state.mem.map(0x5000, 0x5000);

    for (int i = 0; i < 4; i++) {
        SP::linux64* s = (SP::linux64*)(state.ForkState(20));
        z3::expr f1 = s->ctx().bv_const("a1", 8);
        z3::expr f2 = s->ctx().bv_const("a2", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->mem.store(0x602080, 1000 + i);
        s->mem.store(0x602088, 1000 + i);
        if (i == 3)
            s->set_status(Death);
    }
    std::cout << state << std::endl;
    for (int i = 4; i < 5; i++) {
        SP::linux64* s = (SP::linux64*)(state.ForkState(32));
        z3::expr f1 = s->ctx().bv_const("aj", 8);
        z3::expr f2 = s->ctx().bv_const("ak", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->set_status((State_Tag)88);
    }

    std::cout << state << std::endl;
    Int i = 0;
    for (auto s : state.branch) {
        i += 1;
        if (i <= 3) { continue; }
        SP::linux64* s2 = (SP::linux64*)(s->ForkState(20));
        s->set_status(Fork);
        z3::expr f = s2->ctx().bv_const("b", 8);
        s2->solv.add_assert(f > i);
        s2->mem.store(0x602080, 100 + i);
        s2->mem.store(0x602081, 100ull + i + (1ull << 63));
        if (i <= 4)
            continue;
        s2->m_InvokStack.push(787, 87);
    }


    std::cout << state << std::endl;


    cmpr::Context64 c = state.cmprContext(20, NewState);
    c.add_avoid(Death);
    c.add_avoid((State_Tag)88);

    state.compress(c);
    std::cout << state << std::endl;
    return true;
}

//
//bool test_dirty_cmpress() {
//    ctx64 v(VexArchAMD64, PROJECT_DIR"PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.xml");
//    SP::linux64 state(v, 0, True);
//
//
//    UChar bf[] = { 0xD9 ,0x74 ,0x24 ,0xE2 };
//    for (int i = 0; i < sizeof(bf); i++) {
//        state.mem.Ist_Store(state.get_cpu_ip() + i, bf[i]);
//    }
//    Vns f = state.m_ctx.bv_const("b", 64);
//    state.solv.add_assert(f != 0);
//    state.regs.Ist_Put(AMD64_IR_OFFSET::FPTAG, f);
//    state.start();
//
//    std::cout << state << std::endl;
//    return true;
//}
//

bool check(TRsolver &solver, sbool &&s) {
    solver.add(s);
    auto f = solver.check();
    if (!(f == z3::unsat)) {
        std::cout << solver.assertions() << std::endl;
        std::cout << solver.get_model() << std::endl;
        solver.pop();
        return false;
    }
    solver.pop();
    return true;
}



bool test_ir_dirty_rflags() {
    z3::context c;
    TRsolver solver(c);
    {
        ssbval<64> dep1(c.bv_const("dep1", 64));
        ssbval<64> dep2(c, c.bv_const("dep2", 64));
        ssbval<64> ndep(c, c.bv_const("ndep", 64));


        solver.add((z3_amd64g_calculate_condition(rsval<uint64_t>(c, AMD64CondLE), rsval<uint64_t>(c, AMD64G_CC_OP_SUBB), dep1, dep2, ndep).tos().extract<0, 0>() == 1) != dep1.extract<7,0>() <= dep2.extract<7, 0>());
        if (solver.check() != z3::unsat) return false;
        solver.pop();


        solver.add((z3_amd64g_calculate_condition(rsval<uint64_t>(c, AMD64CondLE), rsval<uint64_t>(c, AMD64G_CC_OP_SUBQ), dep1, dep2, ndep).tos().extract<0, 0>() == 1) != dep1 <= dep2);
        if (solver.check() != z3::unsat) return false;
        solver.pop();

    };
    {
        subval<64> dep1(c.bv_const("dep1", 64));
        subval<64> dep2(c, c.bv_const("dep2", 64));
        subval<64> ndep(c, c.bv_const("ndep", 64));

        solver.add((z3_amd64g_calculate_condition(rsval<uint64_t>(c, AMD64CondBE), rsval<uint64_t>(c, AMD64G_CC_OP_SUBB), dep1, dep2, ndep).tos().extract<0, 0>() == 1) != dep1.extract<7, 0>() <= dep2.extract<7, 0>());
        if (solver.check() != z3::unsat) return false;
        solver.pop();


        solver.add((z3_amd64g_calculate_condition(rsval<uint64_t>(c, AMD64CondB), rsval<uint64_t>(c, AMD64G_CC_OP_SUBQ), dep1, dep2, ndep).tos().extract<0, 0>() == 1) != dep1 < dep2);
        if (solver.check() != z3::unsat) return false;
        solver.pop();

    };

    {

        ssbval<8> dep1(c.bv_const("dep1", 8));
        ssbval<8> dep2(c, c.bv_const("dep2", 8));
        subval<64> ndep(c, c.bv_const("ndep", 64));;

        sbool s0 = z3_amd64g_calculate_condition(rsval<uint64_t>(c, AMD64CondLE), rsval<uint64_t>(c, AMD64G_CC_OP_SUBL), dep1.ext<true, 24>() - 0xa, ssbval<64>(c, 0x55), ndep).tos().extract<0, 0>() == 1;
        sbool s1 = z3_amd64g_calculate_condition(rsval<uint64_t>(c, AMD64CondLE), rsval<uint64_t>(c, AMD64G_CC_OP_SUBB), dep1.to_ubv(), ssbval<64>(c, 0x2f), ndep).tos().extract<0, 0>() == 1;
        sbool s2 = z3_amd64g_calculate_condition(rsval<uint64_t>(c, AMD64CondLE), rsval<uint64_t>(c, AMD64G_CC_OP_SUBB), dep1.to_ubv(), ssbval<64>(c, 0x39), ndep).tos().extract<0, 0>() == 1;
            
        cbool_assert( check(solver, !s0 != (dep1.ext<true, 24>() - 0xa) > ssbval<32>(c, 0x55)));
        cbool_assert(check(solver, !s1 != dep1 > ssbval<8>(c, 0x2f)));
        cbool_assert(check(solver, s2 != dep1 <= ssbval<8>(c, 0x39)));
        
    }


    std::cout << std::endl;
    return true;
}
bool test_mem_at(int base) {

    //static_assert(sizeof(VexGuestX86State) % 16 == 0, "error align"); 


    ctx32 v(VexArchX86, "");
    SP::win32 state(v, 0, True);
    state.mem.map(base - 0x1000,  0x2000);
    state.mem.map(0x0000026db91e2770,  0x2000);


    subval<64> v64 = state.ctx().bv_const("v64", 64);
    ssbval<32> v32 = state.ctx().bv_const("v32", 32);

    state.mem.store(base - 2, v64);
    auto c = (state.mem.load<Ity_I64>(base - 2).tos() == v64).simplify();

    if (!c.real()) {
        std::cout << c << std::endl;
        return false;
    }
    if (!c.tor()) {
        std::cout << c << std::endl;
        return false;
    }

    SP::win32 fork(&state, 0x1000);
    auto tv64 = v64.translate(fork.ctx());
    auto tv32 = v32.translate(fork.ctx());

    c = (fork.mem.load<Ity_I64>(base - 2).tos() == tv64).simplify();
    if (!c.real())
        return false;
    if (!c.tor())
        return false;

    fork.mem.store(base - 2, tv32);

    c = (fork.mem.load<Ity_I64>(base - 2).tos() == tv64.extract<63, 32>().concat(tv32)).simplify();
    if (!c.real())
        return false;
    if (!c.tor())
        return false;


    for (int i = 0; i <= 20; i++) {

        SP::win32 fork(&state, 0x1000);

    }
    return true;
}

bool test_mem() {

    bool a = test_mem_at(0x1000);
    bool b = test_mem_at(0x1000 + 0x500);
    return a&&b;
}

bool test_mem_GPMana() {
    z3::context ctx;
    cmpr::GPMana v1(ctx, 18);
    subval<64> v64 = ctx.bv_const("v64", 64);
    ssbval<32> v32 = ctx.bv_const("v32", 32);
    for (int i = 0; i < 5; i++) {
        v1.add(v32 > i, v64 + i);
        v1.debug_display();
    }
    for (int i = 5; i < 10; i++) {
        v1.add(v32 < i, v64 + (i - 5));
        v1.debug_display();
    }

    v1.add(v32 < 9, v64 + 3);
    v1.add(v32 < 9, v64 + 9);
    v1.debug_display();

    std::cout << v1.get() << std::endl;
    return true;
}

bool test_code_no_linear() {
    ctx64 v(VexArchAMD64, "");
    SP::linux64 state(v, 0, True);
    //state.setFlag(CF_traceJmp);
    state.setFlag(CF_ppStmts);

    state.mem.map(0x1000, 0x6000);
    /* xor rax,rax  48 31 C0
    *  add rax, 0x7f237234   48 05 34 72 23 7F
    * 
    */
    int i;
    ULong vic = 0x8000;
    for (i = 0; i <= 0x1000/2; i++) {
        state.mem.store(0x1900 + i * 6, 0x7f2372340548);
        vic += 0x7f237234;
    }

    state.mem.store(0x1900 + i * 6, 0xf4);

    state.regs.set(AMD64_IR_OFFSET::RAX, 0x8000ll);
    state.start(0x1900);

    auto rax = state.regs.get<false, 64, Z3_BV_SORT>(AMD64_IR_OFFSET::RAX);

    return (rax.tor() == vic);
}
//#define TESTZ3

#ifdef TESTZ3
#include "test/example.hpp"

void z3_lean() {

    std::cout << "consequence example\n";
    context c;
    expr A = c.bv_const("a", 8);
    expr B = c.bv_const("b", 8);
    expr C = c.bv_const("c", 8);
    solver s(c);
    s.add((A>B));
    s.add((B>=C));
    expr_vector assumptions(c), vars(c), consequences(c);
    assumptions.push_back(C<B);
    vars.push_back(A);
    vars.push_back(B);
    vars.push_back(C);
    std::cout << s.consequences(assumptions, vars, consequences) << "\n";
    std::cout << vars << "\n";
    std::cout << consequences << "\n";
}


void recfun_example_2() {
    std::cout << "recfun example\n";
    context c;
    expr i = c.int_const("i");
    expr x = c.int_const("x");
    expr ix = c.int_const("ix");
    sort I = c.int_sort();
    sort B = c.bool_sort();

    sort dom[] = { I, I, I };
    func_decl f = c.recfun(c.str_symbol("f"), 3, dom, I);

    expr_vector args(c);
    args.push_back(i); args.push_back(x); args.push_back(ix);
    c.recdef(f, args, ite(i<=ix, f( i*2+2 , x+i*i , ix), x+i));
    model m(c);
    expr zero_numeral = c.int_val(0);
    expr one_numeral = c.int_val(1);
    //m.add_const_interp(f, zero_numeral);
    std::cout << f(c.int_val(12), c.int_val(5), c.int_val(5000)).simplify() << std::endl;;
    prove(f(c.int_val(0), i, c.int_val(0)) > 0);
}

#endif












int main() {

#ifdef TESTZ3
    recfun_example_2();
    testz3();
#endif
    IR_TEST(test_basic_var_real);
    IR_TEST(test_basic_var_sym);

    //testz3();
    IR_TEST(test_mem_GPMana);
    IR_TEST(test_mem);
    IR_TEST(test_code_no_linear);
    IR_TEST(test_ir_dirty_rflags);
    IR_TEST(test_ir_dirty);
    IR_TEST(creakme);
    IR_TEST(asong);
    IR_TEST(test_cmpress);

}

//int main() {
//    {
//        flag_max_count = 38+6;
//        flag_count = 0;
//
//        StatePrinter<StateAMD64> state(INIFILENAME, 0, True);
//        state.hook_add(0x400CC0, success_ret3);
//        StateAnalyzer gv(state);
//        gv.Run();
//    };
//    return 0;
//}

//
//int main() {
//    flag_max_count = 1;
//    flag_count = 0;
//
//    StatePrinter<StateX86> state(INIFILENAME, 0, True);
//
//    context& c = state;
//
//    for (int i = 0; i < 32; i++) {
//        auto flag = state.get_int_const(8);
//        auto ao1 = flag >= 'a' && flag <= 'f';
//        auto ao3 = flag >= '0' && flag <= '9';
//        state.mem.Ist_Store(i + 0x0019F554, flag);
//        state.add_assert(ao1 || ao3, 1);
//        if (i == 31) {
//            _VexGuestX86State reg(state);
//            state.mem.Ist_Store(reg.guest_EBP-0x24, flag);
//        }
//    }
//
//
//    state.hook_add(0x4050B0, Dea);
//    state.hook_add(0x4050D0, success_ret2);
//
//    State::pushState(state);
//    State::pool->wait();
//
//    return 0;
//}


//

