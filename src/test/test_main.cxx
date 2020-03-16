
#include "test.h"

using namespace TR;



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
State_Tag success_ret3(State<Addr64>* s) {
    s->solv.push();
    UChar bf[] = { 0xEC, 0x29, 0xE3, 0x41, 0xE1, 0xF7, 0xAA, 0x1D, 0x29, 0xED, 0x29, 0x99, 0x39, 0xF3, 0xB7, 0xA9, 0xE7, 0xAC, 0x2B, 0xB7, 0xAB, 0x40, 0x9F, 0xA9, 0x31, 0x35, 0x2C, 0x29, 0xEF, 0xA8, 0x3D, 0x4B, 0xB0, 0xE9, 0xE1, 0x68, 0x7B, 0x41 };

    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RDI);
    for (int i = 0; i < 38; i++) {
        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
        s->solv.add(e == (UChar)bf[i]);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == z3::sat) {
        vex_printf("issat");
        auto m = s->solv.get_model();
        std::cout << m << std::endl;
        exit(0);
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    
    s->solv.pop();
    return Death;
}
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

Vns flag_limit(Vns& flag) {
    char flags_char[] = "@_-{}1:() ^";
    Vns re = Vns(flag, flags_char[0]) == flag;
    for (int i = 1; i < sizeof(flags_char); i++) {
        re = re || (Vns(flag, flags_char[i]) == flag);
    }
    auto ao1 = flag >= 'a' && flag <= 'z';
    auto ao2 = flag >= 'A' && flag <= 'Z';
    auto ao3 = flag >= '0' && flag <= '9';
    return re || ao1 || ao2 || ao3;
}



State_Tag test_ir_dirty_hook(State<Addr32>& state) {
    UInt esp = 0x8000 - 532;
    PWOW64_CONTEXT ContextRecord = (PWOW64_CONTEXT)(esp - sizeof(WOW64_CONTEXT));
    PEXCEPTION_RECORD32 ExceptionRecord = (PEXCEPTION_RECORD32)(esp - sizeof(WOW64_CONTEXT) - sizeof(EXCEPTION_RECORD32));

    if ((UInt)state.vex_stack_get(1) != (Addr32)(ULong)ContextRecord) return Death;
    if ((UInt)state.vex_stack_get(2) != EXCEPTION_BREAKPOINT) return Death;
    if ((UInt)state.vex_stack_get(22 + offsetof(WOW64_CONTEXT, Esp) / 4) != 0x8000) return Death;
    return Exit;
}

bool test_ir_dirty() {
    ctx32 v(VexArchX86, "");
    v.set_system(windows);
    v.setFlag(CF_traceJmp);
    v.setFlag(CF_ppStmts);
    v.param().set("ntdll_KiUserExceptionDispatcher", 0x2000);

    SP::X86 state(v, 0, True);
    state.mem.map(0x1000, 0x2000);
    state.mem.map(0x5000, 0x5000);
    state.hook_add(0x2000, test_ir_dirty_hook);
    state.mem.Ist_Store(0x1000, 0xcc);

    state.regs.Ist_Put(X86_IR_OFFSET::ESP, 0x8000);
    state.regs.Ist_Put(X86_IR_OFFSET::EIP, 0x1000);
    state.regs.Ist_Put(X86_IR_OFFSET::CC_OP, 0x0);


    state.start(0x1000);

    return state.status() == Exit;
}

bool creakme();
bool asong();
bool creakme_exception_test

bool test_cmpress() {
    ctx64 v(VexArchAMD64, "");
    SP::AMD64 state(v, 0, True);

    state.mem.map(0x602000, 0x2000);
    state.mem.map(0x5000, 0x5000);

    for (int i = 0; i < 4; i++) {
        SP::AMD64* s = (SP::AMD64*)(state.ForkState(20));
        Vns f1 = s->m_ctx.bv_const("a1", 8);
        Vns f2 = s->m_ctx.bv_const("a2", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->mem.Ist_Store(0x602080, 1000 + i);
        s->mem.Ist_Store(0x602088, 1000 + i);
        if (i == 3)
            s->set_status(Death);
    }
    std::cout << state << std::endl;
    for (int i = 4; i < 5; i++) {
        SP::AMD64* s = (SP::AMD64*)(state.ForkState(32));
        Vns f1 = s->m_ctx.bv_const("aj", 8);
        Vns f2 = s->m_ctx.bv_const("ak", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->set_status((State_Tag)88);
    }

    std::cout << state << std::endl;
    UInt i = 0;
    for (auto s : state.branch) {
        i += 1;
        if (i <= 3) { continue; }
        SP::AMD64* s2 = (SP::AMD64*)(s->ForkState(20));
        s->set_status(Fork);
        Vns f = s2->m_ctx.bv_const("b", 8);
        s2->solv.add_assert(f > i);
        s2->mem.Ist_Store(0x602080, 100 + i);
        s2->mem.Ist_Store(0x602081, 100ull + i + (1ull << 63));
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


bool test_dirty_cmpress() {
    ctx64 v(VexArchAMD64, PROJECT_DIR"PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.xml");
    SP::AMD64 state(v, 0, True);


    //extern
    //    IRDirty* unsafeIRDirty_0_N(Int regparms, const HChar * name, void* addr,
    //        IRExpr * *args);

    ///* Similarly, make a zero-annotation dirty call which returns a value,
    //   and assign that to the given temp. */
    //extern
    //    IRDirty* unsafeIRDirty_1_N(IRTemp dst,
    //        Int regparms, const HChar * name, void* addr,
    //        IRExpr * *args);


    UChar bf[] = { 0xD9 ,0x74 ,0x24 ,0xE2 };
    for (int i = 0; i < sizeof(bf); i++) {
        state.mem.Ist_Store(state.get_cpu_ip() + i, bf[i]);
    }
    Vns f = state.m_ctx.bv_const("b", 64);
    state.solv.add_assert(f != 0);
    state.regs.Ist_Put(AMD64_IR_OFFSET::FPTAG, f);
    state.start();

    std::cout << state << std::endl;
    return true;
}
int main() {
    //testz3();
    //IR_TEST(test_ir_dirty);
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

