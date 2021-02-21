#include "test.h"

using namespace TR;

static State_Tag hook(State& s) {


    //s.setFlags(CF_None);

    return Running;
}

static State_Tag hook2(State& s) {
    int ecx = s.regs.get<Ity_I32>(AMD64_IR_OFFSET::RCX).tor();
    int edi = s.regs.get<Ity_I32>(AMD64_IR_OFFSET::RDI).tor();
    int esi = s.regs.get<Ity_I32>(AMD64_IR_OFFSET::RSI).tor();
    //if (ecx < 10) {

    s.setFlag(CF_traceJmp);
    s.setFlag(CF_ppStmts);
    //
    
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

rsval<Long> symbolic_read(StateBase &s, const rsval<ULong>& addr, const rsval<Long>& count) {
    int n = 0;
    for (; n < 10; n++) {
        auto FLAG = s.mk_int_const(8).tos<false, 8>();
        s.mem.Ist_Store(addr + n, FLAG);
        /*auto ao1 = FLAG >= 'A' && FLAG <= 'Z';
        auto ao2 = FLAG >= 'a' && FLAG <= 'z';
        auto ao3 = FLAG >= '0' && FLAG <= '9';
        auto ao4 = FLAG == 0xD || FLAG == 0xA;
        s.solv.add_assert(ao1 || ao2 || ao3 || ao4);*/
    }
    auto res_count = s.mk_int_const(8).tors<false, 8>();
    s.solv.add_assert( (res_count < 12).tos() );
    return res_count;
}

bool test_creakme() {

    vex_context v(-1);
    v.param().set("ntdll_KiUserExceptionDispatcher", (void*)0x777B3BC0);
    v.param().set("Kernel", gen_kernel(Ke::OS_Kernel_Kd::OSK_Windows));
    TR::State state(v, VexArchX86);
    state.read_bin_dump("Y:\\vmp\\Project1.vmp.exe.dump");
    v.hook_read(symbolic_read);

    //state.setFlag(CF_traceJmp);
    //v.hook_read(read);
    //state.setFlag(CF_ppStmts);
    auto dd = &state.get_regs_maps()->guest.amd64;
    state.avoid_anti_debugging();

    //005671c8 0f31            rdtsc
   // v.hook_add(0x76F91778, hook2);
    //v.hook_add(0x74c922fc, nullptr, CF_ppStmts);
    
    //state.hook_add(0x756EEFC5, hoo);

    //state.regs.set()

    state.start();
    if (state.status() != Exit) {
        std::cerr << "guest create exception error" << std::endl;
    }

    /*state.set_status(NewState);
    state.start();*/

    if (state.status() != Exit) {
        std::cerr << "guest create exception error" << std::endl;
    }
    return true;
}