#include "test.h"

using namespace TR;

static State_Tag hoo(StateBase&s) {

    auto eax = s.regs.get<Ity_I32>(X86_IR_OFFSET::EAX);
    auto esi = s.regs.get<Ity_I32>(X86_IR_OFFSET::ESI);
    
    return Exit;
}

static State_Tag hook2(State& s) {
   /* s.setFlag(CF_traceJmp);
    s.setFlag(CF_ppStmts);*/
    auto m64 = s.mem.load<Ity_I64>(0x756EF004);
    
    return Running;
}

//
//
//static rsval<Addr32> read(State<Addr32>& s, const rsval<Addr32>&addr, const rsval<Addr32>& len) {
//    z3::context& ctx = s;
//    for (int n = 0; n < 27; n++) {
//        tval FLAG = s.mk_int_const(8);
//        s.mem.Ist_Store(addr + n, FLAG);
//        auto ao1 = FLAG >= "A" && FLAG <= "Z";
//        auto ao2 = FLAG >= "a" && FLAG <= "z";
//        auto ao3 = FLAG >= "0" && FLAG <= "9";
//        s.solv.add_assert(ao1 || ao2 || ao3 || FLAG == "_" || FLAG == "{" || FLAG == "}", True);
//    }
//    s.mem.Ist_Store(addr + 27, "\n");
//    return Vns(ctx, 28);
//}

bool test_creakme() {

    vex_context v(-1);
    v.param().set("ntdll_KiUserExceptionDispatcher", (void*)0x777B3BC0);
    v.param().set("Kernel", gen_kernel(Ke::OS_Kernel_Kd::OSK_Windows));
    TR::State state(v, VexArchX86);
    state.read_bin_dump("C:\\Users\\Notify\\Desktop\\CrakeMe.exe.dump");
    //state.setFlag(CF_traceJmp);
    //v.hook_read(read);
    //state.setFlag(CF_ppStmts);
    state.avoid_anti_debugging();

    auto sd = state.mem.load<Ity_I64>(0x004023ec);

    v.hook_add(0x756EEFC5, hook2);
    //state.hook_add(0x756EEFC5, hoo);

    //state.regs.set()

    auto m64 = state.mem.load<Ity_I64>(0x756EF004);
    state.start();
    if (state.status() != Exit) {
        std::cerr << "guest create exception error" << std::endl;
    }

    /*state.set_status(NewState);
    state.start();*/

    if (state.status() != Exit) {
        std::cerr << "guest create exception error" << std::endl;
    }

}