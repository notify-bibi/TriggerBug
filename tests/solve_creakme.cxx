#include "test.h"
#include <forward_list>

#include "instopt/engine/irsb_cache.h"
#include <spdlog/async.h>
using namespace TR;


void vmp_reback(State& s);

static State_Tag hook(State& s) {


    //s.setFlags(CF_None);

    return Running;
}

static State_Tag hook2(State& s) {
    int ecx = s.regs.get<Ity_I32>(AMD64_IR_OFFSET::RCX).tor();
    int edi = s.regs.get<Ity_I32>(AMD64_IR_OFFSET::RDI).tor();
    int esi = s.regs.get<Ity_I32>(AMD64_IR_OFFSET::RSI).tor();
    //if (ecx < 10) {

    s.get_trace()->setFlag(CF_traceJmp);
    s.get_trace()->setFlag(CF_ppStmts);
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


namespace TIR {
    class IRStmt {
        IRStmtTag m_tag;
    public:
        IRStmt(IRStmtTag tag) {

        }
    };
    class WrTmp :public IRStmt {
        UInt m_tmp;
        sv::tval m_value;
    public:
        WrTmp(UInt tmp):IRStmt(Ist_WrTmp){}

    };

}


// 高级反编译 人看
class AstBlock {
    typedef typename std::pair<Int, Int> key_value_pair_t;
    std::list<key_value_pair_t> m_param; // regOffset size
    std::list<key_value_pair_t> m_result; // regOffset size

    typedef typename std::list<key_value_pair_t>::iterator list_iterator_t;
    irsb_chunk m_block;
    IRJumpKind m_jmpkind;
public:
    AstBlock(irsb_chunk irsb_chunk) :m_block(irsb_chunk) {
        IRSB* irsb = m_block->get_irsb();
        m_jmpkind = irsb->jumpkind;
        // Z3_mk_string
        Int i;
        for (i = 0; i < irsb->stmts_used; i++) {
            IRStmt* st = irsb->stmts[i];
            //Int i;
            IRDirty* d, * d2;
            IRCAS* cas, * cas2;
            IRPutI* puti, * puti2;
            IRLoadG* lg;
            IRStoreG* sg;
            switch (st->tag) {
            case Ist_Put: {
                update_interval(m_result, st->Ist.Put.offset, sizeofIRType(typeOfIRExpr(irsb->tyenv, st->Ist.Put.data)));
                setHints_Expr(st->Ist.Put.data);
                break;
            }
            case Ist_PutI: {
                puti = st->Ist.PutI.details;
                IRRegArray* descr = puti->descr;
                update_interval(m_result, descr->base, descr->nElems * sizeofIRType(descr->elemTy));
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
                if (cas->expdHi) setHints_Expr(cas->expdHi);
                setHints_Expr(cas->expdLo);
                if (cas->dataHi) setHints_Expr(cas->dataHi);
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
                    if (d->fxState[j].fx == Ifx_Modify
                        || d->fxState[j].fx == Ifx_Write) {
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
                }
                else {
                    vassert(d2->mAddr == NULL);
                }
                setHints_Expr(d2->guard);
                for (i = 0; d2->args[i]; i++) {
                    IRExpr* arg = d2->args[i];
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
    typedef
        struct {
        Bool present;
        Int  low;
        Int  high;
    }
    Interval;

    inline void update_interval(std::list<key_value_pair_t>& i, Int offset, Int size)
    {
        vassert(size > 0);
        Int lo2 = offset;
        Int hi2 = offset + size - 1;
        list_iterator_t it = i.begin();
        for (; it != i.end();) {
            Int lo = it->first;
            Int hi = it->second;
            // over
            if ((lo >= lo2 && lo <= hi2) || (lo2 >= lo && lo2 <= hi)) {
                if (lo > lo2) lo = lo2;
                if (hi < hi2) hi = hi2;
                it = i.erase(it);
                update_interval(i, lo, hi - lo + 1);
                return;
            }
            it++;
        }
        i.push_back(key_value_pair_t(lo2, hi2));
    }

    void setHints_Expr(IRExpr* e)
    {
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
            IRRegArray* descr = e->Iex.GetI.descr;
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
    virtual ~AstBlock() {

    }
};



extern "C" void libvex_BackEnd(const VexTranslateArgs * vta,
    /*MOD*/ VexTranslateResult * res,
    /*MOD*/ IRSB * irsb,
    VexRegisterUpdates pxControl);


auto emu_one_irsb(Addr &guest_start, std::deque<TR::State::BtsRefType>& tmp_branch, TR::State_Tag& m_status, State& s, irsb_chunk irsb) {
    Vex_Kind vkd;
    //ppIRSB(irsb);
    s.get_trace()->traceIRSB(s, guest_start, irsb);
    if (s.vinfo().is_mode_32()) {
        vkd = s.emu_irsb<32>(tmp_branch, guest_start, m_status, irsb);
    }
    else {
        vkd = s.emu_irsb<64>(tmp_branch, guest_start, m_status, irsb);
    }
    s.get_trace()->traceIrsbEnd(s, irsb);
    return vkd;
}




namespace z3 {
    class MemArray : public expr{
        context& m_ctx;
    public:
        MemArray(z3::context& ctx, const char * name) :m_ctx(ctx), expr(ctx, ctx.constant(name, ctx.array_sort(ctx.bv_sort(64), ctx.bv_sort(8)))) {

        }
        template<int ea_nbits>
        void store(const subval<ea_nbits>& ea, const tval & v) {
            z3::store(*this, expr(m_ctx, ea), expr(m_ctx, v));
        }

        template<int ea_nbits>
        expr load(const subval<ea_nbits>& ea, int nbits) {
            expr v = select(*this, expr(m_ctx, ea));
            for (int i = 1; i < (nbits >> 3); i++) {
                v = concat(select(*this, expr(m_ctx, ea + i)), v);
            }
            return v;
        }
    };
}

class IROpt {

    class oMem {
    public:
        using memTy = std::pair<subval<64>, tval>;
        std::deque<memTy> mem_map;

        

        void Ist_Store(sv::tval const& address, sv::tval const& data) {  };
        sv::tval Iex_Load(const sv::tval& address, int nbits) {  };
        sv::tval Iex_Load(const sv::tval& address, IRType ty) {  };
    };

    class oRegs {
    public:

        void Ist_Put(UInt offset, sv::tval const& ir) {  }
        sv::tval Iex_Get(UInt offset, IRType ty){  }
    };

    template<int ea_nbits>
    class StateData : public VMemBase {
        friend class StateBase;
        friend class State;
        oMem& m_mem;
        VRegs& m_regs;
    public:
        StateData(oMem& mem, VRegs& regs) : m_mem(mem), m_regs(regs) {};
        void Ist_Store(sv::tval const& address, sv::tval const& data) override { m_mem.Ist_Store(address.tors<false, ea_nbits>(), data); };
        sv::tval Iex_Load(const sv::tval& address, int nbits) override { return m_mem.Iex_Load(address.tors<false, ea_nbits>(), nbits); };
        sv::tval Iex_Load(const sv::tval& address, IRType ty) override { return m_mem.Iex_Load(address.tors<false, ea_nbits>(), ty); };

        void Ist_Put(UInt offset, sv::tval const& ir) override { m_regs.Ist_Put(offset, ir); }
        sv::tval Iex_Get(UInt offset, IRType ty) override { return m_regs.Iex_Get(offset, ty); }
        virtual ~StateData() {}
    };

    const vex_context& m_vctx;
    TR::State& m_state;
    z3::vcontext& m_ctx;   // z3 prove
    VRegs regs;
    TRsolver solv;
    oMem mem;
    std::shared_ptr<EmuEnvironment> m_irvex;
    
public:
    IROpt(TR::State& s):m_vctx(s.vctx()), m_state(s), m_ctx(s.ctx()), solv(s.ctx()), regs(s.ctx(), REGISTER_LEN){
        m_irvex = std::make_shared<EmuEnvGuest>(s.vctx(), s.vinfo(), s.mem);
        s.set_mem_access(std::make_shared<IROpt::StateData<32>>(mem, regs));
    }

    inline EmuEnvironment& irvex() { return *m_irvex.get(); }

    inline sv::tval ILGop(const IRLoadG* lg) {
        switch (lg->cvt) {
        case ILGop_IdentV128: { return mem.Iex_Load(tIRExpr(lg->addr), Ity_V128);            }
        case ILGop_Ident64: { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I64);            }
        case ILGop_Ident32: { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I32);            }
        case ILGop_16Uto32: { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I16).zext(16);   }
        case ILGop_16Sto32: { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I16).sext(16);   }
        case ILGop_8Uto32: { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I8).zext(8);    }
        case ILGop_8Sto32: { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I8).sext(8);    }
        case ILGop_INVALID:
        default: VPANIC("ppIRLoadGOp");
        }
    }

    tval tIRExpr(IRExpr* e) {
        switch (e->tag) {
        case Iex_Get: { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
        case Iex_RdTmp: { return irvex().operator[](e->Iex.RdTmp.tmp); }
        case Iex_Unop: { return tUnop(e->Iex.Unop.op, tIRExpr(e->Iex.Unop.arg)); }
        case Iex_Binop: { return tBinop(e->Iex.Binop.op, tIRExpr(e->Iex.Binop.arg1), tIRExpr(e->Iex.Binop.arg2)); }
        case Iex_Triop: { return tTriop(e->Iex.Triop.details->op, tIRExpr(e->Iex.Triop.details->arg1), tIRExpr(e->Iex.Triop.details->arg2), tIRExpr(e->Iex.Triop.details->arg3)); }
        case Iex_Qop: { return tQop(e->Iex.Qop.details->op, tIRExpr(e->Iex.Qop.details->arg1), tIRExpr(e->Iex.Qop.details->arg2), tIRExpr(e->Iex.Qop.details->arg3), tIRExpr(e->Iex.Qop.details->arg4)); }
        case Iex_Load: { return mem.Iex_Load(tIRExpr(e->Iex.Load.addr), e->Iex.Get.ty); }
        case Iex_Const: { return sv::tval(m_ctx, e->Iex.Const.con); }
        case Iex_ITE: {
            auto cond = tIRExpr(e->Iex.ITE.cond).tobool();
            if (cond.real()) {
                if (cond.tor()) {
                    return tIRExpr(e->Iex.ITE.iftrue);
                }
                else {
                    return tIRExpr(e->Iex.ITE.iffalse);
                }
            }
            else {
                return ite(cond.tos(), tIRExpr(e->Iex.ITE.iftrue), tIRExpr(e->Iex.ITE.iffalse));
            }
        }
       // case Iex_CCall: { return tCCall(e->Iex.CCall.cee, e->Iex.CCall.args, e->Iex.CCall.retty); }
        case Iex_GetI: {
            auto ix = tIRExpr(e->Iex.GetI.ix);   /*  [e->Iex.GetI.ix, e->Iex.GetI.bias];  */
            if (ix.real()) {
                int re_ix = ix.tor<true, 32>();
                UInt regoff = e->Iex.GetI.descr->base + (((UInt)(e->Iex.GetI.bias + re_ix)) % e->Iex.GetI.descr->nElems) * ty2length(e->Iex.GetI.descr->elemTy);
                return regs.Iex_Get(regoff, e->Iex.GetI.descr->elemTy);
            }
        };
       // case Iex_GSPTR: { return sv::tval(m_ctx, getGSPTR(), sizeof(HWord) << 3); };
        case Iex_Binder: {
            Int binder = e->Iex.Binder.binder;
            spdlog::critical("tIRExpr Iex_Binder:  {}", binder);
        }
        case Iex_VECRET: { }
        default:
            spdlog::critical("tIRExpr error:  {}", e->tag);
            VPANIC("not support");
        }
    }

    void tIRStmt(const IRTypeEnv* tyenv, const IRStmt* s)
    {

        switch (s->tag) {
        case Ist_WrTmp: { irvex()[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data); break; };
        case Ist_Put: { regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
        case Ist_Store: { mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; };
        case Ist_PutI: {
            // PutI(840:8xI8)[t10,-1]
            // 840:arr->base
            // 8x :arr->nElems
            // I8 :arr->elemTy
            // t10:ix
            // -1 :e->Iex.GetI.bias
            auto ix = tIRExpr(s->Ist.PutI.details->ix);
            if (ix.real()) {
                int re_ix = ix.tor<true, 32>();
                UInt regoff = s->Ist.PutI.details->descr->base + (((UInt)((s->Ist.PutI.details->bias + re_ix))) % s->Ist.PutI.details->descr->nElems) * ty2length(s->Ist.PutI.details->descr->elemTy);
                regs.Ist_Put(
                    regoff,
                    tIRExpr(s->Ist.PutI.details->data)
                );
            }
            else {
                vassert(0);
            }
            break;
        }
        case Ist_LoadG: { // load with guard
            IRLoadG* lg = s->Ist.LoadG.details;
            auto guard = tIRExpr(lg->guard).tobool();
            if LIKELY(guard.real()) {
                irvex()[lg->dst] = (guard.tor()) ? ILGop(lg) : tIRExpr(lg->alt);
            }
            else {
                irvex()[lg->dst] = ite(guard.tos(), ILGop(lg), tIRExpr(lg->alt));
            }
            break;
        }
        case Ist_StoreG: { // store with guard
            IRStoreG* sg = s->Ist.StoreG.details;
            auto addr = tIRExpr(sg->addr);
            auto guard = tIRExpr(sg->guard).tobool();
            auto data = tIRExpr(sg->data);
            if LIKELY(guard.real()) {
                if (guard.tor()) {
                    mem.Ist_Store(addr, data);
                }
            }
            else {
                mem.Ist_Store(addr, ite(guard.tos(), mem.Iex_Load(addr, data.nbits()), data));
            }
            break;
        }
        case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
            //  t15   = CASle(t31 ::t12   ->t13)
            //  oldLo = CASle(addr::expdLo->dataLo)
            //  解释
            //  oldLo = *addr  t15 = *t31
            //  *addr = dataLo *t31 = t13
            IRCAS cas = *(s->Ist.CAS.details);
            auto addr = tIRExpr(cas.addr);//r10.value
            sv::tval expdLo = tIRExpr(cas.expdLo);
            sv::tval dataLo = tIRExpr(cas.dataLo);
            if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
                sv::tval expdHi = tIRExpr(cas.expdHi);
                sv::tval dataHi = tIRExpr(cas.dataHi);
                irvex()[cas.oldHi] = mem.Iex_Load(addr, expdLo.nbits());
                irvex()[cas.oldLo] = mem.Iex_Load(addr, expdLo.nbits());
                mem.Ist_Store(addr, dataLo);
                if (addr.nbits() == 32) {
                    mem.Ist_Store(sv::tval(addr.tors<false, 32>() + (dataLo.nbits() >> 3)), dataHi);
                }else{
                    mem.Ist_Store(sv::tval(addr.tors<false, 64>() + (dataLo.nbits() >> 3)), dataHi);
                }
            }
            else {//single
                irvex()[cas.oldLo] = mem.Iex_Load(addr, expdLo.nbits());
                mem.Ist_Store(addr, dataLo);
            }
            break;
        }
        case Ist_Dirty: {
            IRDirty* dirty = s->Ist.Dirty.details;
            rsbool guard = tIRExpr(dirty->guard).tobool();
            if UNLIKELY(guard.symb()) {
                VPANIC("auto guard = tIRExpr(dirty->guard); symbolic");
            }
            if LIKELY(guard.tor()) {
                IRType tmpTy = dirty->tmp == IRTemp_INVALID ? Ity_INVALID : typeOfIRTemp(tyenv, dirty->tmp);
                //dirty_call_run(dirty->tmp, tmpTy, dirty);
            }
            break;// fresh changed block
        }
        case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/ {
            ppIRMBusEvent(s->Ist.MBE.event);
            break;
        }
        case Ist_LLSC:
        default: {
            spdlog::critical("what ppIRStmt {}", s->tag);
            VPANIC("what ppIRStmt");
        }
        };
    }


    void emu_irsb(IRSB* irsb, bool is_mode32) {


        Addr guest_start = -1;
        UInt IMark_stmtn = 0;
        ULong EAmask = is_mode32 ? fastMask(32) : fastMask(64);
        const IRStmt* s = irsb->stmts[0];
        for (UInt stmtn = 0; stmtn < irsb->stmts_used; s = irsb->stmts[++stmtn])
        {
            ppIRStmt(s);
            printf("\n");
            switch (s->tag)
            {
            case Ist_NoOp: break;
            case Ist_IMark: {
                guest_start = s->Ist.IMark.addr & EAmask;
                IMark_stmtn = stmtn;
                break;
            };
            case Ist_AbiHint: { 
                break;
            }
            case Ist_Exit: {
                rsbool guard = tIRExpr(s->Ist.Exit.guard).tobool();
                if LIKELY(guard.real()) {
                    if LIKELY(guard.tor()) {
                    Exit_guard_true:
                        if (s->Ist.Exit.jk == Ijk_Boring)
                        {
                            guest_start = s->Ist.Exit.dst->Ico.U64 & EAmask;
                        }
                        else {
                            if UNLIKELY(s->Ist.Exit.dst->Ico.U64 & EAmask == guest_start) { // 异常循环
                                ppIRSB(irsb);
                            }
                        }
                    };
                }
                else {
                    int ebool = eval_all_bool(solv, guard.tos());
                    if (ebool < 0) {
                        throw Expt::SolverNoSolution("eval_size <= 0", solv);
                    }
                    if (ebool == 1) {
                        goto Exit_guard_true;
                    }
                    if (ebool == 2) {
                    }
                }
                break;
            }
            default:
                tIRStmt(irsb->tyenv, s);
            }

        }


    }


    void optimization_by_z3(IRSB* sb) {









    }




};





















rsval<Long> symbolic_read_no_as(StateBase& s, const rsval<ULong>& addr, const rsval<Long>& count) {
    int n = 0;
    for (; n < 10; n++) {
        auto FLAG = s.mk_int_const(8).tos<false, 8>();
        s.mem.Ist_Store(addr + n, FLAG);
    }
    return rsval<Long>(s.ctx(), 6);
}


static State_Tag print_simplify(State& s) {
    const char bf[] = { 7, 4, 4, 15, 53, 71, 81, 87, 122 };

    auto enc = s.regs.get<Ity_I32>(AMD64_IR_OFFSET::RBP) - 0x50;
    for (int i = 0; i < sizeof(bf); i++) {
        auto e = s.mem.load<Ity_I8>(enc + i);
        s.solv.add(e == (UChar)bf[i]);

        std::cout << e.tos().simplify() << std::endl;
    }
    printf("checking\n\n");
    auto dfdfs = s.solv.check();
    if (dfdfs == z3::sat) {
        printf("issat");
        auto m = s.solv.get_model();
        std::cout << m << std::endl;
        std::cout << s.solv << std::endl;
    }
    else {
        printf("unsat?????????? %d", dfdfs);
        std::cout << s.solv << std::endl;
    }

    s.solv.pop();
    return Death;
    std::cout << "run vmp insns count " << s.insn_count << std::endl;
    return Running;
}



bool test_creakme() {
#if 1

#else

    vex_context v(4);
    v.param().set("ntdll_KiUserExceptionDispatcher", std::make_shared<TR::sys_params_value>((size_t)0x777B3BC0));
    v.param().set("Kernel", gen_kernel(Ke::OS_Kernel_Kd::OSK_Windows));
    TR::State state(v, VexArchX86);
    state.read_bin_dump("Z:\\vmp\\vmpbackup\\creakme.exe.dump");


    state.get_trace()->setFlag(CF_ppStmts);
    auto count = rcval<UInt>(state.ctx(), 9);
    auto input_ea = state.vex_stack_get<UInt>(1);
    symbolic_read_no_as(state, input_ea, count);
    v.hook_add(0x411912, print_simplify);

    state.start();
    /*TESTCODE(
        vmp_reback(state);
    )*/

#endif
    test_creakme1();
    return true;
}

