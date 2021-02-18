#include "test.h"
#include "engine/guest_layout_helper.h"


using namespace TR;



State_Tag success_ret3(StateBase& s) {
    UChar bf[] = { 0xEC, 0x29, 0xE3, 0x41, 0xE1, 0xF7, 0xAA, 0x1D, 0x29, 0xED, 0x29, 0x99, 0x39, 0xF3, 0xB7, 0xA9, 0xE7, 0xAC, 0x2B, 0xB7, 0xAB, 0x40, 0x9F, 0xA9, 0x31, 0x35, 0x2C, 0x29, 0xEF, 0xA8, 0x3D, 0x4B, 0xB0, 0xE9, 0xE1, 0x68, 0x7B, 0x41 };

    auto enc = s.regs.get<Ity_I64>(AMD64_IR_OFFSET::RDI);
    for (int i = 0; i < 38; i++) {
        auto e = s.mem.load<Ity_I8>(enc + i);
        s.solv.add(e == (UChar)bf[i]);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s.solv.check();
    if (dfdfs == z3::sat) {
        vex_printf("issat");
        auto m = s.solv.get_model();
        std::cout << m << std::endl;
        exit(0);
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    
    s.solv.pop();
    return Death;
}



bool asong() {
   // vex_context<Addr64> v(VexArchAMD64, 8, PROJECT_DIR"PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.dump");
   // SP::linux64 state(v, 0, True);
   // state.setFlag(CF_ppStmts);
   // state.setFlag(CF_traceJmp);
   // std::cout << state << std::endl;
   // for (int i = 0; i < 38; i++) {
   //     auto flag = state.mk_int_const(8).tos<false, 8>();
   //     auto g = flag >= 1u && flag <= 128u;
   //     state.mem.store(state.regs.get<Ity_I64>(AMD64_IR_OFFSET::RDI) + i, flag);
   //     state.solv.add_assert(g);
   // }
   // state.hook_add(0x400CC0, success_ret3);


   // test(state);
   //// state.start();



}