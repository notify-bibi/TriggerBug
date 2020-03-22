#include "test.h"

using namespace TR;

bool asong() {
    vex_context<Addr64> v(VexArchAMD64, PROJECT_DIR"PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.dump");



    SP::linux64 state(v, 0, True);
    std::cout << state << std::endl;

    Kernel& k = state;

    State<Addr64>* pp = k;


    test(state);
    //state.start();

    //TRGL::VexGuestAMD64State reg(state);
    ///*for (int i = 0; i < 38; i++) {
    //    auto flag = state.mk_int_const(8);
    //    auto ao3 = flag >= 1 && flag <= 128;
    //    state.mem.Ist_Store(reg.guest_RDI + i, flag);
    //    state.solv.add_assert(ao3);
    //}*/
    //state.hook_add(0x400CC0, success_ret3);

}