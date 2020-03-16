#include "test.h"

using namespace TR;

State_Tag hoo(State<Addr32> &s) {

    Vns eax = s.regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::EAX);
    Vns esi = s.regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::ESI);
    
    return Exit;
}



bool creakme_exception_test() {
    ctx32 v(VexArchX86, PROJECT_DIR"PythonFrontEnd\\examples\\SCTF-creakMe\\creakme.exe.dump");
    v.set_system(windows);
    v.setFlag(CF_traceJmp);
    //v.setFlag(CF_ppStmts);
    v.param().set("ntdll_KiUserExceptionDispatcher", 0x774F4200);

    SP::X86 state(v, 0, True);

    Vns sd = state.mem.Iex_Load(0x004023ec, Ity_I64);

    state.hook_add(0x04023EF, hoo);
    state.start();

    if (state.status() != Exit) {
        std::cerr << "guest create exception error" << std::endl;
    }



}