

#include "instopt/engine/state_explorer.h"
#include "instopt/helper/z3_target_call.h"
#include "gen_global_var_call.hpp"
#include "instopt/engine/irsb_cache.h"
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/ADT/ImmutableMap.h"
#include "instopt/engine/vexStateHelper.h"
#include "instopt/tracer/BlockView.h"
#include <instopt/tracer/CFGTracer.h>


using namespace TR;


namespace TIR {
class IRStmt {
  IRStmtTag m_tag;

public:
  IRStmt(IRStmtTag tag) {}
};
class WrTmp : public IRStmt {
  UInt m_tmp;
  sv::tval m_value;

public:
  WrTmp(UInt tmp) : IRStmt(Ist_WrTmp) {}
};

} // namespace TIR


class VisitIRSB {
  VisitIRSB() {}
  void visit(IRSB *irsb) {
    Int i;
    for (i = 0; i < irsb->stmts_used; i++) {
      IRStmt *st = irsb->stmts[i];
      // Int i;
      IRDirty *d, *d2;
      IRCAS *cas, *cas2;
      IRPutI *puti, *puti2;
      IRLoadG *lg;
      IRStoreG *sg;
      switch (st->tag) {
      case Ist_Put: {
        update_interval(
            m_result, st->Ist.Put.offset,
            sizeofIRType(typeOfIRExpr(irsb->tyenv, st->Ist.Put.data)));
        setHints_Expr(st->Ist.Put.data);
        break;
      }
      case Ist_PutI: {
        puti = st->Ist.PutI.details;
        IRRegArray *descr = puti->descr;
        update_interval(m_result, descr->base,
                        descr->nElems * sizeofIRType(descr->elemTy));
        setHints_Expr(puti->ix);
        setHints_Expr(puti->data);
        break;
      }
      case Ist_WrTmp:
        setHints_Expr(st->Ist.WrTmp.data);
        break;
      case Ist_Store:
        setHints_Expr(st->Ist.Store.addr);
        setHints_Expr(st->Ist.Store.data);
        break;
      case Ist_StoreG:
        sg = st->Ist.StoreG.details;
        setHints_Expr(sg->addr);
        setHints_Expr(sg->data);
        setHints_Expr(sg->guard);
        break;
      case Ist_LoadG:
        lg = st->Ist.LoadG.details;
        setHints_Expr(lg->addr);
        setHints_Expr(lg->alt);
        setHints_Expr(lg->guard);
        break;
      case Ist_CAS:
        cas = st->Ist.CAS.details;
        setHints_Expr(cas->addr);
        if (cas->expdHi)
          setHints_Expr(cas->expdHi);
        setHints_Expr(cas->expdLo);
        if (cas->dataHi)
          setHints_Expr(cas->dataHi);
        setHints_Expr(cas->dataLo);
        break;
      case Ist_LLSC:
        setHints_Expr(st->Ist.LLSC.addr);
        setHints_Expr(st->Ist.LLSC.storedata);
        break;
      case Ist_Dirty:
        d = st->Ist.Dirty.details;

        Int j;
        for (j = 0; j < d->nFxState; j++) {
          if (d->fxState[j].fx == Ifx_Modify || d->fxState[j].fx == Ifx_Write) {
            Int offset = d->fxState[i].offset;
            Int size = d->fxState[i].size;
            Int nRepeats = d->fxState[i].nRepeats;
            Int repeatLen = d->fxState[i].repeatLen;
            update_interval(m_result, offset, nRepeats * repeatLen + size);
          }
        }

        d2 = emptyIRDirty();
        *d2 = *d;
        d2->args = shallowCopyIRExprVec(d2->args);
        if (d2->mFx != Ifx_None) {
          setHints_Expr(d2->mAddr);
        } else {
          vassert(d2->mAddr == NULL);
        }
        setHints_Expr(d2->guard);
        for (i = 0; d2->args[i]; i++) {
          IRExpr *arg = d2->args[i];
          if (LIKELY(!is_IRExpr_VECRET_or_GSPTR(arg)))
            setHints_Expr(arg);
        }
        break;
      case Ist_NoOp:
      case Ist_MBE:
      case Ist_IMark:
        break;
      case Ist_AbiHint:
        setHints_Expr(st->Ist.AbiHint.base);
        setHints_Expr(st->Ist.AbiHint.nia);
        break;
      case Ist_Exit:
        setHints_Expr(st->Ist.Exit.guard);

        if (st->Ist.Exit.jk == Ijk_Boring) {
          Addr next = st->Ist.Exit.dst->Ico.U64;
          if (st->Ist.Exit.dst->tag == Ico_U32)
            next = (UInt)next;
        }

        break;
      default:
        VPANIC("flatten_Stmt");
      };
    }
  }
};

// 高级反编译 人看
class AstBlock {
  typedef typename std::pair<Int, Int> key_value_pair_t;
  std::list<key_value_pair_t> m_param;  // regOffset size
  std::list<key_value_pair_t> m_result; // regOffset size

  typedef typename std::list<key_value_pair_t>::iterator list_iterator_t;
  irsb_chunk m_block;
  IRJumpKind m_jmpkind;

public:
  AstBlock(irsb_chunk irsb_chunk) : m_block(irsb_chunk) {
    IRSB *irsb = m_block->get_irsb();
    m_jmpkind = irsb->jumpkind;
    // Z3_mk_string
    Int i;
    for (i = 0; i < irsb->stmts_used; i++) {
      IRStmt *st = irsb->stmts[i];
      // Int i;
      IRDirty *d, *d2;
      IRCAS *cas, *cas2;
      IRPutI *puti, *puti2;
      IRLoadG *lg;
      IRStoreG *sg;
      switch (st->tag) {
      case Ist_Put: {
        update_interval(
            m_result, st->Ist.Put.offset,
            sizeofIRType(typeOfIRExpr(irsb->tyenv, st->Ist.Put.data)));
        setHints_Expr(st->Ist.Put.data);
        break;
      }
      case Ist_PutI: {
        puti = st->Ist.PutI.details;
        IRRegArray *descr = puti->descr;
        update_interval(m_result, descr->base,
                        descr->nElems * sizeofIRType(descr->elemTy));
        setHints_Expr(puti->ix);
        setHints_Expr(puti->data);
        break;
      }
      case Ist_WrTmp:
        setHints_Expr(st->Ist.WrTmp.data);
        break;
      case Ist_Store:
        setHints_Expr(st->Ist.Store.addr);
        setHints_Expr(st->Ist.Store.data);
        break;
      case Ist_StoreG:
        sg = st->Ist.StoreG.details;
        setHints_Expr(sg->addr);
        setHints_Expr(sg->data);
        setHints_Expr(sg->guard);
        break;
      case Ist_LoadG:
        lg = st->Ist.LoadG.details;
        setHints_Expr(lg->addr);
        setHints_Expr(lg->alt);
        setHints_Expr(lg->guard);
        break;
      case Ist_CAS:
        cas = st->Ist.CAS.details;
        setHints_Expr(cas->addr);
        if (cas->expdHi)
          setHints_Expr(cas->expdHi);
        setHints_Expr(cas->expdLo);
        if (cas->dataHi)
          setHints_Expr(cas->dataHi);
        setHints_Expr(cas->dataLo);
        break;
      case Ist_LLSC:
        setHints_Expr(st->Ist.LLSC.addr);
        setHints_Expr(st->Ist.LLSC.storedata);
        break;
      case Ist_Dirty:
        d = st->Ist.Dirty.details;

        Int j;
        for (j = 0; j < d->nFxState; j++) {
          if (d->fxState[j].fx == Ifx_Modify || d->fxState[j].fx == Ifx_Write) {
            Int offset = d->fxState[i].offset;
            Int size = d->fxState[i].size;
            Int nRepeats = d->fxState[i].nRepeats;
            Int repeatLen = d->fxState[i].repeatLen;
            update_interval(m_result, offset, nRepeats * repeatLen + size);
          }
        }

        d2 = emptyIRDirty();
        *d2 = *d;
        d2->args = shallowCopyIRExprVec(d2->args);
        if (d2->mFx != Ifx_None) {
          setHints_Expr(d2->mAddr);
        } else {
          vassert(d2->mAddr == NULL);
        }
        setHints_Expr(d2->guard);
        for (i = 0; d2->args[i]; i++) {
          IRExpr *arg = d2->args[i];
          if (LIKELY(!is_IRExpr_VECRET_or_GSPTR(arg)))
            setHints_Expr(arg);
        }
        break;
      case Ist_NoOp:
      case Ist_MBE:
      case Ist_IMark:
        break;
      case Ist_AbiHint:
        setHints_Expr(st->Ist.AbiHint.base);
        setHints_Expr(st->Ist.AbiHint.nia);
        break;
      case Ist_Exit:
        setHints_Expr(st->Ist.Exit.guard);

        if (st->Ist.Exit.jk == Ijk_Boring) {
          Addr next = st->Ist.Exit.dst->Ico.U64;
          if (st->Ist.Exit.dst->tag == Ico_U32)
            next = (UInt)next;
        }

        break;
      default:
        VPANIC("flatten_Stmt");
      };
    }
  }
  typedef struct {
    Bool present;
    Int low;
    Int high;
  } Interval;

  inline void update_interval(std::list<key_value_pair_t> &i, Int offset,
                              Int size) {
    vassert(size > 0);
    Int lo2 = offset;
    Int hi2 = offset + size - 1;
    list_iterator_t it = i.begin();
    for (; it != i.end();) {
      Int lo = it->first;
      Int hi = it->second;
      // over
      if ((lo >= lo2 && lo <= hi2) || (lo2 >= lo && lo2 <= hi)) {
        if (lo > lo2)
          lo = lo2;
        if (hi < hi2)
          hi = hi2;
        it = i.erase(it);
        update_interval(i, lo, hi - lo + 1);
        return;
      }
      it++;
    }
    i.push_back(key_value_pair_t(lo2, hi2));
  }

  void setHints_Expr(IRExpr *e) {
    Int i;
    switch (e->tag) {
    case Iex_CCall:
      for (i = 0; e->Iex.CCall.args[i]; i++)
        setHints_Expr(e->Iex.CCall.args[i]);
      return;
    case Iex_ITE:
      setHints_Expr(e->Iex.ITE.cond);
      setHints_Expr(e->Iex.ITE.iftrue);
      setHints_Expr(e->Iex.ITE.iffalse);
      return;
    case Iex_Qop:
      setHints_Expr(e->Iex.Qop.details->arg1);
      setHints_Expr(e->Iex.Qop.details->arg2);
      setHints_Expr(e->Iex.Qop.details->arg3);
      setHints_Expr(e->Iex.Qop.details->arg4);
      return;
    case Iex_Triop:
      setHints_Expr(e->Iex.Triop.details->arg1);
      setHints_Expr(e->Iex.Triop.details->arg2);
      setHints_Expr(e->Iex.Triop.details->arg3);
      return;
    case Iex_Binop:
      setHints_Expr(e->Iex.Binop.arg1);
      setHints_Expr(e->Iex.Binop.arg2);
      return;
    case Iex_Unop:
      setHints_Expr(e->Iex.Unop.arg);
      return;
    case Iex_Load:
      setHints_Expr(e->Iex.Load.addr);
      return;
    case Iex_Get: {
      update_interval(m_param, e->Iex.Get.offset, sizeofIRType(e->Iex.Get.ty));
      return;
    }
    case Iex_GetI: {
      IRRegArray *descr = e->Iex.GetI.descr;
      Int size = sizeofIRType(descr->elemTy);
      update_interval(m_param, descr->base, descr->nElems * size);
      setHints_Expr(e->Iex.GetI.ix);
      return;
    }
    case Iex_RdTmp:
    case Iex_Const:
      return;
    default:
      VPANIC("setHints_Expr");
    }
  }
  virtual ~AstBlock() {}
};



class BindingKey {
public:
  enum Kind { Default = 0x0, Direct = 0x1 };

private:
  enum { Symbolic = 0x2 };

  llvm::PointerIntPair<const MemRegion *, 2> P;
  uint64_t Data;

  /// Create a key for a binding to region \p r, which has a symbolic offset
  /// from region \p Base.
  explicit BindingKey(const SubRegion *r, const SubRegion *Base, Kind k)
      : P(r, k | Symbolic), Data(reinterpret_cast<uintptr_t>(Base)) {
    assert(r && Base && "Must have known regions.");
    assert(getConcreteOffsetRegion() == Base && "Failed to store base region");
  }

  /// Create a key for a binding at \p offset from base region \p r.
  explicit BindingKey(const MemRegion *r, uint64_t offset, Kind k)
      : P(r, k), Data(offset) {
    assert(r && "Must have known regions.");
    assert(getOffset() == offset && "Failed to store offset");
    assert((r == r->getBaseRegion() || isa<ObjCIvarRegion>(r) ||
            isa<CXXDerivedObjectRegion>(r)) &&
           "Not a base");
  }

public:
  bool isDirect() const { return P.getInt() & Direct; }
  bool hasSymbolicOffset() const { return P.getInt() & Symbolic; }

  const MemRegion *getRegion() const { return P.getPointer(); }
  uint64_t getOffset() const {
    assert(!hasSymbolicOffset());
    return Data;
  }

  const SubRegion *getConcreteOffsetRegion() const {
    assert(hasSymbolicOffset());
    return reinterpret_cast<const SubRegion *>(static_cast<uintptr_t>(Data));
  }

  const MemRegion *getBaseRegion() const {
    if (hasSymbolicOffset())
      return getConcreteOffsetRegion()->getBaseRegion();
    return getRegion()->getBaseRegion();
  }

  void Profile(llvm::FoldingSetNodeID &ID) const {
    ID.AddPointer(P.getOpaqueValue());
    ID.AddInteger(Data);
  }

  static BindingKey Make(const MemRegion *R, Kind k);

  bool operator<(const BindingKey &X) const {
    if (P.getOpaqueValue() < X.P.getOpaqueValue())
      return true;
    if (P.getOpaqueValue() > X.P.getOpaqueValue())
      return false;
    return Data < X.Data;
  }

  bool operator==(const BindingKey &X) const {
    return P.getOpaqueValue() == X.P.getOpaqueValue() && Data == X.Data;
  }

  LLVM_DUMP_METHOD void dump() const;
};

typedef llvm::ImmutableMap<BindingKey, sv::tval> ClusterBindings;
typedef llvm::ImmutableMapRef<BindingKey, sv::tval> ClusterBindingsRef;
class RegionBindingsRef
    : public llvm::ImmutableMapRef<sv::tval, ClusterBindings> {
  ClusterBindings::Factory *CBFactory;
};

namespace {


    class SimpleMem {
        // AST : SVal
        z3::vcontext& ctx;
    public:
        SimpleMem(z3::vcontext& ctx) : ctx(ctx){

        }

        void Ist_Store(sv::tval const& address, sv::tval const& data) {
            llvm::errs() << address.str(true) << " " << data.str(true) << "\n";
            
        };

        sv::tval Iex_Load(const sv::tval& address, int nbits) {
            llvm::errs() << address.str(true) << "\n";
            
        };

        sv::tval Iex_Load(const sv::tval& address, IRType ty) { 
            sv::tval ea = address.zext(64 - address.nbits());
            llvm::errs() << ea.str(true) << "\n";

        };

    };


    class SimpleRegs {
        z3::vcontext& ctx;
        VRegs regs;
        llvm::SparseBitVector<4096> BitVector;
        StateHelper& statehelper;
    public:
        SimpleRegs(z3::vcontext& ctx, UInt size, StateHelper& statehelper) :ctx(ctx), regs(ctx, size), statehelper(statehelper) {
            const char* prev = statehelper.regOff2name(0);
            UInt prevOff = 0;
            for (UInt o = 1; o < size; o++) {
                auto regName = statehelper.regOff2name(o);
                //llvm::errs() << regName <<"\n";
                if (prev != regName) {
                    std::stringstream st;
                    auto regVal = ctx.bv_const(prev, (o - prevOff)<<3);
                    regs.Ist_Put(o, (Z3_ast)regVal, (UInt)(o - prevOff));
                    prev = regName;
                    prevOff = o;
                }
            }
        };
        void init(UInt offset, UInt nbytes) {
            for (int o = offset; o < offset + nbytes; o++) {
                if (BitVector.test(o)) {
                }
                else {
                    BitVector.set(o);
                }
            }
        }

        void Ist_Put(UInt offset, sv::tval const& ir) { 
            // init(offset, ir.nbits() >> 3);
            regs.Ist_Put(offset, ir);
        }
        sv::tval Iex_Get(UInt offset, IRType ty) { 
            // init(offset, ty2length(ty));
            return regs.Iex_Get(offset, ty);
        }
    };



    class MemoryModeling : public VMemBase {
        friend class StateBase;
        friend class State;
        SimpleMem m_mem;
        SimpleRegs m_regs;

    public:
        MemoryModeling(z3::vcontext& ctx, UInt size, StateHelper& statehelper) : m_mem(ctx), m_regs(ctx, size, statehelper) {};
        void Ist_Store(sv::tval const& address, sv::tval const& data) override { m_mem.Ist_Store(address, data); };
        sv::tval Iex_Load(const sv::tval& address, int nbits) override { return m_mem.Iex_Load(address, nbits); };
        sv::tval Iex_Load(const sv::tval& address, IRType ty) override { return m_mem.Iex_Load(address, ty); };

        void Ist_Put(UInt offset, sv::tval const& ir) override { m_regs.Ist_Put(offset, ir); }
        sv::tval Iex_Get(UInt offset, IRType ty) override { return m_regs.Iex_Get(offset, ty); }

        // StateModeling mode_change() { return StateData<to_ea_nbits>(m_mem, m_regs); };
        virtual ~MemoryModeling() { }
    };

    class SimpleEnvGuest : public EmuEnvironment {
        IR_Manager m_ir_temp; 
        GraphView& gv;
    public:
        //init vex
        SimpleEnvGuest(GraphView& gv, Z3_context ctx, VexArch arch) :EmuEnvironment(arch, 0) , m_ir_temp(ctx), gv(gv){};

        void block_integrity(Addr ea, UInt sz) override {  }
        void set_guest_bb_insn_control_obj() override { }

        //void block_integrity(Addr address, UInt insn_block_delta) override;

        //new ir temp
        virtual void malloc_ir_buff(Z3_context ctx) override { }
        //free ir temp
        virtual void free_ir_buff() override { }
        // guest translate
        irsb_chunk translate_front(HWord guest_addr) override { 

            auto blocks = gv.get_MutiBlocks();
            auto E = blocks.find(guest_addr)->second;
            BlockView& basic_irsb_chunk = E.get()->operator[](0);
            return basic_irsb_chunk.get_irsb_chunk();
        }
        virtual sv::tval& operator[](UInt idx) override { return m_ir_temp[idx]; }
    };

    class StateModeling {
    public:
      VMemBase mem_access;
      SimpleEnvGuest IrEnv;
      StateModeling(vex_context &vctx, VexArch guest_arch,
                    StateHelper &statehelper)
          : mem_access(ctx(), 4096, statehelper),
            irvex(gv, ctx(), VexArchAMD64){};
      SimpleEnvGuest &irvex() { return IrEnv; }
      void explore(GraphView &gv, const BlockView &entry) {
        irsb_chunk irsb_chunk = entry.get_irsb_chunk();
        std::deque<BtsRefType> tmp_branch;
        Addr guest_start = irsb_chunk->get_bb_base();
        State_Tag status = Running;

        Vex_Kind vkd;

        do {
          irsb_chunk = IrEnv.translate_front(guest_start);
          IRSB *irsb = irsb_chunk->get_irsb();
          ppIRSB(irsb);
          


        } while (vkd == TR::Vex_Kind::vUpdate);
      }

      ~StateModeling() {}
    };



}



void testfd(GraphView& gv, vex_context& vctx, VexArch guest_arch, StateHelper& statehelper, const BlockView& entry) {
    StateModeling SM(vctx, guest_arch, statehelper);
    SM.explore(gv, entry);
}
