#include "test.h"

using namespace TR;

State_Tag hoo(State<Addr32> &s) {

    auto eax = s.regs.get<Ity_I32>(X86_IR_OFFSET::EAX);
    auto esi = s.regs.get<Ity_I32>(X86_IR_OFFSET::ESI);
    
    return Exit;
}

State_Tag hook2(State<Addr32>& s) {
    SP::win32& sp = (SP::win32&)s;
    sp.setFlag(CF_traceJmp);
    return Running;
}

//
//
//static rsval<Addr32> read(State<Addr32>& s, const rsval<Addr32>&addr, const rsval<Addr32>& len) {
//    z3::context& ctx = s;
//    for (int n = 0; n < 27; n++) {
//        tval FLAG = s.mk_int_const(8);
//        s.mem.Ist_Store(addr + n, FLAG);
//        auto ao1 = FLAG >= 'A' && FLAG <= 'Z';
//        auto ao2 = FLAG >= 'a' && FLAG <= 'z';
//        auto ao3 = FLAG >= '0' && FLAG <= '9';
//        s.solv.add_assert(ao1 || ao2 || ao3 || FLAG == '_' || FLAG == '{' || FLAG == '}', True);
//    }
//    s.mem.Ist_Store(addr + 27, '\n');
//    return Vns(ctx, 28);
//}


bool creakme() {
    ctx32 v(VexArchX86, PROJECT_DIR"PythonFrontEnd\\examples\\SCTF-creakMe\\creakme.exe.dump");
    v.set_system(windows);
    //v.setFlag(CF_traceJmp);
    v.param().set("ntdll_KiUserExceptionDispatcher", 0x774F4200);
    //v.hook_read(read);


    SP::win32 state(v, 0, True);



    state.setFlag(CF_ppStmts);

    auto sd = state.mem.load<Ity_I64>(0x004023ec);

    state.hook_add(0x04023EF, hoo);
    state.hook_add(0x0401264, hook2);
    state.start();

    if (state.status() != Exit) {
        std::cerr << "guest create exception error" << std::endl;
    }

    state.set_status(NewState);
    state.start();

    if (state.status() != Exit) {
        std::cerr << "guest create exception error" << std::endl;
    }

}