
#include "../test.h"
#include "instopt/tracer/CFGTracer.h"
#include "instopt/utils/BitCodeUtil.h"
#include <vexllvm/vexhelpers.h>

using namespace TR;


rsval<Long> symbolic_read(StateBase &s, const rsval<ULong> &addr,
                          const rsval<Long> &count) {
  int n = 0;
  for (; n < 10; n++) {
    auto FLAG = s.mk_int_const(8).tos<false, 8>();
    s.mem.Ist_Store(addr + n, FLAG);
    auto ao1 = FLAG >= 'A' && FLAG <= 'Z';
    auto ao2 = FLAG >= 'a' && FLAG <= 'z';
    auto ao3 = FLAG >= '0' && FLAG <= '9';
    auto ao4 = FLAG == 0xD || FLAG == 0xA;
    s.solv.add_assert(ao1 || ao2 || ao3 || ao4);
  }
  auto res_count = s.mk_int_const(8).tors<false, 8>();
  s.solv.add_assert((res_count < 12).tos());
  return rsval<Long>(s.ctx(), 6);
}




static State_Tag statistics(State &s) {

  std::cout << "run vmp insns count " << s.insn_count << std::endl;
  return Running;
}



void testfd(GraphView& gv, vex_context& vctx, VexArch guest_arch, StateHelper& statehelper, const BlockView& entry);
void compile(GraphView& gv, BlockView& basic_irsb_chunk);


void vmp_reback(State &s) {
  GraphView gv(s.vctx());
  gv.explore_block(&s);
  s.vctx().pool().wait();


  


  auto blocks = gv.get_MutiBlocks();
  auto E = blocks.find(0x47f82f)->second;
  BlockView& basic_irsb_chunk = E.get()->operator[](0);
  auto sh = StateHelper::get(VexArchAMD64);
  testfd(gv, s.vctx(), basic_irsb_chunk.get_irsb_chunk()->get_arch(), *sh, basic_irsb_chunk);
  compile(gv, basic_irsb_chunk);
  // ---------------------------------------
  // GenLLVM::getGenLLVM()->getBuilder()
  remill::StoreModuleIRToFile(&GenLLVM::getGenLLVM()->getModule(), "vmp.ll",
                              false);
  // clang -emit-llvm -S vmp.bc -o vmp.ll
  remill::StoreModuleToFile(&GenLLVM::getGenLLVM()->getModule(), "vmp.bc",
                            false);
  // llc.exe -filetype=obj -O3 ./vmp.bc -o vmp3.o



  //gv.simplify();

  gv.ppGraphView(true);
  std::string Dots = gv.creat_graph();
  std::ofstream Dot;
  Dot.open("examplex.dot");
  Dot << Dots;
  Dot.close();

  spdlog::info("state:{}", (std::string)s);
};


bool test_creakme() {
  vex_context v(4);
  v.param().set("ntdll_KiUserExceptionDispatcher",
                std::make_shared<TR::sys_params_value>((size_t)0x777B3BC0));
  v.param().set("Kernel", gen_kernel(Ke::OS_Kernel_Kd::OSK_Windows));
  TR::State state(v, VexArchX86);
  state.read_bin_dump(TESTCASEDIR "\\vmp\\vmpbackup\\creakme.vmp.exe.dump");

#if 1
  // state.get_trace()->setFlag(CF_traceInvoke);
  // v.hook_read(read);
  v.hook_read(symbolic_read);
  state.get_trace()->setFlag(CF_ppStmts);
  VexGuestAMD64State &amd64_reg_state = state.get_regs_maps()->guest.amd64;
  // state.avoid_anti_debugging();
  state.set_level(spdlog::level::debug);
  // auto bts = state.start();
  // 005671c8 0f31            rdtsc
  // v.hook_add(0x76F91778, hook2);
  // v.hook_add(0x74c922fc, nullptr, CF_ppStmts);

  v.hook_add(0x411912, statistics);

  // state.regs.set()

  /* z3::MemArray mem(state, "A");
   mem.store(subval<64>(state, 32), tval(subval<8>(state.ctx(), 32)));
   auto va = mem.load(subval<64>(state, 32), 32);
   std::cout << va.simplify() << std::endl;
   IROpt opt(state);
   irsb_chunk ic = opt.irvex().translate_front(0x428a45);*/

  // opt.emu_irsb(ic->get_irsb(), true);

  state.solv.mk_tactic_solver_default(state);

  /*for (int i = 0; i < 1000; i++) {
      TR::State* cld = (TR::State*)state.ForkState(state.get_state_ep());
      TESTCODE(
      cld->start();
      )
          std::cout << "run guest insns count " << cld->insn_count << std::endl;
      delete cld;
  }*/

  // TESTCODE(state.start(););

  TESTCODE(vmp_reback(state);)
  std::cout << "run guest insns count " << state.insn_count << std::endl;

#else
  state.get_trace()->setFlag(CF_ppStmts);
  auto count = rcval<UInt>(state.ctx(), 1);
  auto input_ea = state.vex_stack_get<UInt>(1);
  symbolic_read(state, input_ea, count);

  state.start();
  /*TESTCODE(
      vmp_reback(state);
  )*/

#endif
  return 1;
}

int main() {
    IR_TEST(test_creakme);
}
