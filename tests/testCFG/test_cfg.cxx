
#include "../test.h"
#include "instopt/tracer/CFGTracer.h"
#include "instopt/utils/BitCodeUtil.h"

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

#include "vexllvm/genllvm.h"
#include "vexllvm/Sugar.h"
#include "vexllvm/vexsb.h"
#include "vexllvm/vexstmt.h"
#include "vexllvm/vexexpr.h"
#include "vexllvm/vexcpustate.h"
#include "vexllvm/vexhelpers.h"


using namespace llvm;
class BL {
public:
  BasicBlock *BB;
  const BlockView *BV;
  Value *ret;

  BL() {}
  BL(BasicBlock *BB, const BlockView *BV, Value *ret)
      : BB(BB), BV(BV), ret(ret) {}
  BL(const BL &B) : BB(B.BB), BV(B.BV), ret(B.ret) {}
  void operator=(const BL &B) {
    BB = B.BB;
    BV = B.BV;
    ret = B.ret;
  }
};

class FlatCFG {
    llvm::LLVMContext& ctx;
    std::unique_ptr<llvm::IRBuilder<>> builder;
    llvm::Module&	mod;
    llvm::FunctionType* funcTy = nullptr;
    llvm::Function* cur_f = nullptr;
    llvm::BasicBlock* entry_bb = nullptr;
    llvm::Value* cur_guest_ctx = nullptr;
    Value *pRet;
    std::unordered_map<const BlockView *, llvm::Function *> m_collect;

  public: 
    FlatCFG(llvm::LLVMContext &ctx, llvm::Module & mod) : ctx(ctx), mod(mod) {
        builder = std::make_unique<IRBuilder<>>(ctx);
      mkFuncTy(64);
    }
    
    void mkFuncTy(unsigned N)
    {
        std::vector<Type*>	f_args;
        std::vector<Type*>	types;

        // StructType* guestCtxTy = StructType::create(ctx, types, "guestCtxTy");
        Type* guestCtxTy = GenLLVM::getGenLLVM()->getGuestTy();
        f_args.push_back(PointerType::get(guestCtxTy, 0));

        funcTy = FunctionType::get(builder->getIntNTy(N), f_args, false);

    }

    void beginBB(const char* name)
    {
        assert(entry_bb == NULL && "nested beginBB");
        cur_f = Function::Create(
            funcTy,
            Function::ExternalLinkage,
            name,
            mod);

        // XXX: marking the regctx as noalias could mess up any instrumentation
        // that wants to modify registers, but I'm not sure if that would ever
        // be a thing I'd want to do
        cur_f->arg_begin()->addAttr(Attribute::AttrKind::NoAlias);

        entry_bb = BasicBlock::Create(ctx, "entry", cur_f);
        builder->SetInsertPoint(entry_bb);

        Function::arg_iterator arg = cur_f->arg_begin();

        //arg->addAttr(Attributes(Attributes::NoAlias));
        cur_guest_ctx = &(*arg);

        auto i64ty = Type::getInt64Ty(ctx);
        pRet = builder->CreateAlloca(i64ty, nullptr, "unhandleRet");

#if 0
        Value* Lctx = builder->CreateAlloca(getGuestTy(), nullptr);
        Value* Tmp = builder->CreateLoad(cur_guest_ctx);
        builder->CreateStore(Tmp, Lctx);
        cur_guest_ctx = Lctx;
#endif


        arg++;

    }

    void endBB(Value *retVal) {
        builder->CreateRet(retVal); 
    }

    llvm::Function *emitIRSB(const BlockView &basic_irsb_chunk) {
      auto f = m_collect.find(&basic_irsb_chunk);
      if (f != m_collect.end()) {
        return f->second;
      };
      // ---------------------------------------
      irsb_chunk irsb = basic_irsb_chunk.get_irsb_chunk();
      VexArch arch = irsb->get_arch();
      VexHelpers::getVexHelpers()->loadDefaultModules(arch);
      GenLLVM::getGenLLVM()->mkFuncTy(
          basic_irsb_chunk.get_irsb_chunk()->get_numBits());
      guest_ptr guest_addr;
      VexSB sb(guest_addr, irsb->get_irsb());
      std::stringstream st;
      st << "bb_" << std::hex
         << basic_irsb_chunk.get_irsb_chunk()->get_bb_base() << "_" << std::dec
         << basic_irsb_chunk.get_irsb_chunk()->get_bb_base();
      llvm::Function *F = sb.emit(st.str().c_str());
      // ---------------------------------------
      return F;
    }

    Value *mkGuard(guest_ptr p, unsigned numBits, Value *L) { 
       Value *ptr = ConstantInt::get(getGlobalContext(), APInt(numBits, p));
      return builder->CreateICmpEQ(L, ptr);
    }

    
    Value *SaveRet(Value *V) {
      Value *ret;
      unsigned sz = V->getType()->getIntegerBitWidth();
      if (sz != 64) { 
        ret = builder->CreateZExt(V, IntegerType::get(ctx, 64));
      } else {
        ret = V;
      }
      builder->CreateStore(ret, pRet);
      return ret;
    }



    void emitNext(Value *v_cmp, const BlockView *next, BasicBlock* bb) {
      BasicBlock *bb_then, *bb_else, *bb_origin;

      bb_origin = builder->GetInsertBlock();
      bb_then = BasicBlock::Create(getGlobalContext(), "if_then",
                                   bb_origin->getParent());
      bb_else = BasicBlock::Create(getGlobalContext(), "if_else",
                                   bb_origin->getParent());

      /* evaluate guard condition */
      builder->SetInsertPoint(bb_origin);
      builder->CreateCondBr(v_cmp, bb_then, bb_else);

      /* guard condition return, leave this place */
      /* XXX for calls we're going to need some more info */
      builder->SetInsertPoint(bb_then);

      builder->CreateBr(bb);
      

      /* continue on */
      builder->SetInsertPoint(bb_else);
    }

    //Value *lift(const BlockView *entry) {
    //  const BlockView *curr = entry;
    //  Value *Ret = nullptr;
    //  while (true) {
    //    llvm::Function *F = emitIRSB(*curr);
    //    
    //   /* Ret = builder->CreateCall(F, cur_guest_ctx);
    //    if (curr->get_nexts().size() == 1) {
    //      curr = *curr->get_nexts().begin();
    //    }
    //    for (auto Next : curr->get_nexts()) {
    //      Value *cmp = mkGuard((guest_ptr)Next->get_irsb_chunk()->get_bb_base(),
    //                           Next->get_irsb_chunk()->get_numBits(), Ret);
    //      emitNext(cmp, Next);
    //      
    //    }
    //    if (curr->get_nexts().size() != 1) {
    //      break;
    //    }*/
    //  }
    //  return Ret;
    //}

    void capstone(GraphView GV, const BlockView& entry) {
        beginBB("A_VMP");
        
        std::unordered_map<Addr, BL> map;

        for (auto it = GV.get_blocks().begin(); it != GV.get_blocks().end();
             it++) {
          const BlockView *curr = &it->second;
          llvm::Function *F = emitIRSB(*curr);
          std::stringstream st;
          st << "bb_" << std::hex << curr->get_irsb_chunk()->get_bb_base() << "_"
             << std::dec << curr->get_irsb_chunk()->get_bb_base();

          BasicBlock *bb_then = BasicBlock::Create(getGlobalContext(), st.str().c_str(), entry_bb->getParent());
          builder->SetInsertPoint(bb_then);
          Value *Ret = builder->CreateCall(F, cur_guest_ctx);
          map[curr->get_irsb_chunk()->get_bb_base()] = BL(bb_then, curr, Ret);
        }

        BasicBlock *unhandle = BasicBlock::Create(getGlobalContext(), "unhandle",
                                                  entry_bb->getParent());
        
        for (auto it = GV.get_blocks().begin(); it != GV.get_blocks().end();
             it++) {
          const BlockView *curr = &it->second;
          auto &B = map[curr->get_irsb_chunk()->get_bb_base()];
          builder->SetInsertPoint(B.BB);
          for (auto Nit = curr->get_nexts().begin();
               Nit != curr->get_nexts().end(); Nit++) {
            BlockView *Next = *Nit;
            auto &NB = map[Next->get_irsb_chunk()->get_bb_base()];
            Value *cmp =
                mkGuard((guest_ptr)Next->get_irsb_chunk()->get_bb_base(),
                        curr->get_irsb_chunk()->get_numBits(), B.ret);

            emitNext(cmp, NB.BV, NB.BB);
          }

          SaveRet(B.ret);
          builder->CreateBr(unhandle);
        }

        builder->SetInsertPoint(entry_bb);
        auto &EntryBB = map[entry.get_irsb_chunk()->get_bb_base()];
        BranchInst *Binst = builder->CreateBr(EntryBB.BB);
        // Value *Ret = lift(&entry);
        // endBB(Ret);

        builder->SetInsertPoint(unhandle);
        Value *Ret = builder->CreateLoad(pRet, "ret");
        endBB(Ret);

    };
};





void vmp_reback(State &s) {
  GraphView gv(s.vctx());
  gv.explore_block(&s);
  s.vctx().pool().wait();


  
  StateHelper *sh = getStateHelper();
  // theGenLLVM =
  GenLLVM::getGenLLVM() = std::make_unique<GenLLVM>(*sh);
  VexHelpers::getVexHelpers() = VexHelpers::create(VexArchX86);


  auto blocks = gv.get_MutiBlocks();
  auto E = blocks.find(0x47f82f)->second;
  BlockView& basic_irsb_chunk = E.get()->operator[](0);
  FlatCFG FC(GenLLVM::getGenLLVM()->getContext() , GenLLVM::getGenLLVM()->getModule());
  FC.capstone(gv, basic_irsb_chunk);
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
