#include "engine/ir_dirty.h"
#include "engine/state_class.h"

#ifdef _DEBUG
//#define OUTPUT_STMTS
#endif

using namespace TR;
//注意地址位宽


extern IRSB* LibVEX_FrontEnd_coexistence( /*MOD*/ VexTranslateArgs* vta,
    /*OUT*/ VexTranslateResult* res,
    /*OUT*/ VexRegisterUpdates* pxControl,
    Pap* pap);

extern "C" void vexSetAllocModeTEMP_and_save_curr(void);

class DMEM : public MEM<Addr64> {
    bool m_front;
    Addr64 m_stack_reservve_size;
    Addr64 m_stack_addr;
    Addr64 m_guest_regs_map_addr;

public:
    template<typename ADDR>
    DMEM(vctx_base const& vctxb, TRsolver& s, z3::vcontext& ctx, MEM<ADDR>& mem, bool front, Bool _need_record) : MEM(vctxb, s, ctx, mem.CR3, mem.user, _need_record),
        m_front(front),
        m_stack_reservve_size(0),
        m_stack_addr(0),
        m_guest_regs_map_addr(0)
    {
        vassert(REGISTER_LEN < 0x1000);
    };

    //FORK
    DMEM(z3::solver& so, z3::vcontext& ctx, DMEM& father_mem, Bool _need_record): MEM(so, ctx, father_mem, _need_record),
        m_stack_reservve_size(0),
        m_stack_addr(0),
        m_guest_regs_map_addr(0)
    {
        m_front = false;
    }

    void set_clear(Addr64 srs, Addr64 sa, Addr64 grmd) {
        m_stack_reservve_size = srs;
        m_stack_addr = sa;
        m_guest_regs_map_addr = grmd;
    }

   ~DMEM()
    {
       if(m_front){
           CR3[0] = nullptr;
       }else{
           unmap(m_stack_addr, m_stack_reservve_size);
           unmap(m_guest_regs_map_addr, REGISTER_LEN);
       }
    };

    void store_regs_to_mem(Addr64 guest_regs_map_addr, Register<REGISTER_LEN> &regs_in, IRDirty* d) {
        m_guest_regs_map_addr = guest_regs_map_addr;
        for (Int i = 0; i < d->nFxState; i++) {
            switch (d->fxState[i].fx) {
            case Ifx_None: continue;
            case Ifx_Modify:
            case Ifx_Read: { 
                Ist_Store(m_guest_regs_map_addr + (UInt)d->fxState[i].offset, regs_in.Iex_Get(d->fxState[i].offset, d->fxState[i].size));
                if (d->fxState[i].nRepeats > 0) {
                    for (UInt repeat = 0; repeat < d->fxState[i].nRepeats; repeat++) {
                        Ist_Store(m_guest_regs_map_addr + (UInt)d->fxState[i].offset + (UInt)d->fxState[i].repeatLen * repeat, regs_in.Iex_Get(d->fxState[i].offset, d->fxState[i].size));
                    }
                }
                break; 
            }
            case Ifx_Write: break;
            default: vpanic("ppIREffect");
            }
        }
    }

    void put_regs_from_mem(Register<REGISTER_LEN>& regs_out, IRDirty* d) {
        for (Int i = 0; i < d->nFxState; i++) {
            switch (d->fxState[i].fx) {
            case Ifx_None: continue;
            case Ifx_Modify:
            case Ifx_Write: {
                regs_out.Ist_Put(d->fxState[i].offset, Iex_Load(m_guest_regs_map_addr + (UInt)d->fxState[i].offset, (IRType)(d->fxState[i].size << 3)));
                if (d->fxState[i].nRepeats > 0) {
                    for (UInt repeat = 0; repeat < d->fxState[i].nRepeats; repeat++) {
                        regs_out.Ist_Put(d->fxState[i].offset, Iex_Load(m_guest_regs_map_addr + (UInt)d->fxState[i].offset + (UInt)d->fxState[i].repeatLen * repeat, (IRType)(d->fxState[i].size << 3)));
                    }
                }
                break;
            }
            case Ifx_Read: break;
            default: vpanic("ppIREffect");
            }
        }
    }
};


class DState;
class DStateCmprsInterface;
DState* mk_DStateIRDirty(DState* s);



class DState {
    template <typename xx> friend class VexIRDirty;
    friend class DStateIRDirty;
    friend class DStateCmprsInterface;
    bool m_front;
    DState* m_base;
    vex_info& m_vex_info;
    z3::vcontext _m_z3_ctx;
    TRsolver  _m_z3_solv;
    z3::vcontext& m_ctx;
    TRsolver& m_solv;
    Register<REGISTER_LEN>  regs;
    DMEM                    mem;

    bool    m_dirty_vex_mode = false;
    DState* m_dctx = nullptr;
    Addr64 m_stack_reservve_size = 0x1000;
    Addr64 m_stack_addr;
    Addr64 m_guest_regs_map_addr;

    Addr64 vex_ret_addr = 0x1ull;// Dont patch it
    BranchManager<DState> branch;
    State_Tag   m_status;
    InvocationStack<Addr64>   m_InvokStack;
    UChar* m_host_addr;
    UChar* m_host_ep;
    Vns* m_irtemp = nullptr;
    //fork
    DState(DState& fork) :
        m_front(false),
        m_base(&fork),
        _m_z3_ctx(),
        _m_z3_solv(_m_z3_ctx, fork.m_solv, z3::solver::translate{}),
        m_ctx(_m_z3_ctx),
        m_solv(_m_z3_solv),
        regs(_m_z3_ctx, true),
        mem(_m_z3_solv, _m_z3_ctx, fork.mem, true),
        m_stack_addr(mem.find_block_reverse(fork.m_stack_addr - 0x1000, m_stack_reservve_size)),
        m_guest_regs_map_addr(mem.find_block_forward(fork.m_guest_regs_map_addr + 0x1000, REGISTER_LEN)),
        vex_ret_addr(fork.vex_ret_addr + 1),
        branch(*this, fork.branch),
        m_status(NewState),
        m_host_addr(nullptr),
        m_host_ep(nullptr),
        m_vex_info(fork.m_vex_info)
    {
        mem.map(m_stack_addr, m_stack_reservve_size);
        mem.map(m_guest_regs_map_addr, 1000);
        mem.set_clear(m_stack_reservve_size, m_stack_addr, m_guest_regs_map_addr);
    };

    //fork
    DState(DState& fork, Addr64 oep) :DState(fork) {
        m_host_ep = (UChar*)oep;
        m_host_addr = (UChar*)oep;
    }
public:
    //dirty call
    template<typename ADDR>
    DState(vex_info const& info, z3::vcontext& ctx, TRsolver&solver, MEM<ADDR>& memory) :
        m_front(true),
        m_base(nullptr),
        _m_z3_ctx(),
        _m_z3_solv(ctx),
        m_ctx(ctx),
        m_solv(solver),
        regs(ctx, true),
        mem(info, solver, ctx, memory, true, true),
        m_stack_addr(memory.find_block_reverse((ADDR)0 - 0x10000, m_stack_reservve_size)),
        m_guest_regs_map_addr(memory.find_block_forward(0x1000, REGISTER_LEN)),
        vex_ret_addr(1),
        branch(*this),
        m_status(NewState),
        m_host_addr(nullptr),
        m_host_ep(nullptr),
        m_vex_info(info)
    {
        mem.map(m_stack_addr, m_stack_reservve_size);
        mem.map(m_guest_regs_map_addr, 1000);
        mem.set_clear(m_stack_reservve_size, m_stack_addr, m_guest_regs_map_addr);
    };


    ~DState() {
        if (m_dirty_vex_mode) {
            delete ((DState*)m_dctx);
        }
    };

    inline const vex_info& info() const { return m_vex_info; }
    inline State_Tag    status() { return m_status; }
    inline void         set_status(State_Tag t) { m_status = t; };
    Vns                 CCall(IRCallee* cee, IRExpr** exp_args, IRType ty);
    Vns                 tIRExpr(IRExpr* e);
    IRSB*               translate(UChar* Host_code);
    Vns                 result(IRType ty) { return regs.Iex_Get(AMD64_IR_OFFSET::RAX, ty); }
    inline Addr64       getGSPTR() { return m_guest_regs_map_addr; }
    DState*             mkState(Addr64 ges) { return new DState(*this, ges); }
    void                set_ip(UChar* Haddr) { m_host_addr = Haddr; };
    inline Addr64       get_cpu_ip() { return (Addr64)m_host_addr; }

    virtual bool  StateCompression(DState const&) { return true; }
    virtual void  StateCompressMkSymbol(DState const& ) {  }; 
    inline operator z3::context& () { return m_ctx; }
    inline operator z3::vcontext& () { return m_ctx; }
    inline operator Z3_context() const { return m_ctx; }

    virtual void     store_regs_to_mem(IRDirty* dirty) { mem.store_regs_to_mem(m_guest_regs_map_addr, regs, dirty); }
    virtual void     put_regs_from_mem(IRDirty* dirty) { mem.put_regs_from_mem(regs, dirty); }
    virtual Vns      base_tIRExpr(IRExpr* e) { return m_base->tIRExpr(e).translate(m_ctx); }
    virtual IRSB*    translate(
        /*MOD*/ VexTranslateArgs* vta,
        /*OUT*/ VexTranslateResult* res,
        /*OUT*/ VexRegisterUpdates* pxControl,
        Pap* pap
    ) {
        return LibVEX_FrontEnd_coexistence(vta, res, pxControl, pap);
    }
    void             init_param(IRCallee* cee, IRExpr** exp_args) {
        set_ip((UChar*)cee->addr);
        Addr64 stack_ret = m_stack_addr + m_stack_reservve_size - 0x8ull * 6;
        regs.Ist_Put(AMD64_IR_OFFSET::RSP, stack_ret);
        regs.Ist_Put(AMD64_IR_OFFSET::RBP, 0x233ull);
        {
            //x64 fastcall 
            const UInt assembly_args[] = { AMD64_IR_OFFSET::RCX, AMD64_IR_OFFSET::RDX, AMD64_IR_OFFSET::R8, AMD64_IR_OFFSET::R9 };
            for (UInt i = 0; exp_args[i] != NULL; i++) {
                if (i >= (sizeof(assembly_args) / sizeof(UInt))) {
                    mem.Ist_Store(stack_ret - ((ULong)i << 3), base_tIRExpr(exp_args[i]));
                }
                else {
                    regs.Ist_Put(assembly_args[i], base_tIRExpr(exp_args[i]));
                }
            };
        };
        //code : call cee->addr
        vex_push(vex_ret_addr);
    }



    DState*         getDirtyVexCtx() {
        if (!m_dirty_vex_mode) {
            m_dirty_vex_mode = true;
            m_dctx = mk_DStateIRDirty(this);
        }
        return m_dctx;
    }
    void            dirty_ccall(IRCallee* cee, IRExpr** args) {
        Int regparms = cee->regparms;
        UInt mcx_mask = cee->mcx_mask;
        m_dctx->init_param(cee, args);
        ThreadPool p(1);
        p.enqueue([this] {
            m_dctx->start();
            });
    }
    void            dirty_run(IRDirty* dirty) {
        m_dctx->store_regs_to_mem(dirty);
        m_dctx->dirty_ccall(dirty->cee, dirty->args);
        m_dctx->put_regs_from_mem(dirty);
    }
    Vns            dirty_call(IRCallee* cee, IRExpr** exp_args, IRType ty) {
        getDirtyVexCtx();
        dirty_ccall(cee, exp_args);
        return result(ty);
    }

    template<typename T>
    void vex_push(T v) {
        Vns sp = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RSP) - 0x8ull;
        regs.Ist_Put(AMD64_IR_OFFSET::RSP, sp);
        mem.Ist_Store(sp, (ULong)v);
    }
    template<>
    void vex_push(Vns const& v) {
        Vns sp = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RSP) - 0x8ull;
        regs.Ist_Put(AMD64_IR_OFFSET::RSP, sp);
        mem.Ist_Store(sp, v);
    }

    Vns vex_pop() {
        Vns sp = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RSP) + 0x8ull;
        regs.Ist_Put(AMD64_IR_OFFSET::RSP, sp);
        return mem.Iex_Load(sp, sp);
    }

    inline Vns ILGop(IRLoadG* lg) {
        switch (lg->cvt) {
        case ILGop_IdentV128: { return mem.Iex_Load(tIRExpr(lg->addr), Ity_V128);         }
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

private:
        
    void exec() {
        EmuEnvironment<MAX_IRTEMP> emu(info(), m_ctx, VexArchAMD64);
        m_irtemp = emu;
        DState* newBranch = nullptr;
        set_status(Running);

        while (true) {
            if (reinterpret_cast<Addr64>(m_host_addr) == vex_ret_addr) {
                Addr64 stack_ret = m_stack_addr + m_stack_reservve_size - 0x8ull * 6;
                Vns rsp = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RSP);
                if (rsp.real()) {
                    vassert((ULong)rsp == stack_ret);
                    set_status(Dirty_ret);
                    break;
                }
                VPANIC("????");
            }
        For_Begin:
            emu.set_host_addr((Addr64)m_host_addr);
            VexRegisterUpdates pxControl;
            VexTranslateResult res;
            IRSB* irsb = translate(emu, &res, &pxControl, emu);
            IRStmt* s = irsb->stmts[0];
            for (Int stmtn = 0; stmtn < irsb->stmts_used;
                s = irsb->stmts[++stmtn])
            {
#ifdef OUTPUT_STMTS
                vex_printf("host-vex ::: ");
                ppIRStmt(s);
#endif
                switch (s->tag) {
                case Ist_Put: { regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
                case Ist_Store: { mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; };
                case Ist_WrTmp: {
                    emu[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data);
#ifdef OUTPUT_STMTS
                    std::cout << emu[s->Ist.WrTmp.tmp];
#endif
                    break; };
                case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
                    IRCAS cas = *(s->Ist.CAS.details);
                    Vns addr = tIRExpr(cas.addr);//r10.value
                    Vns expdLo = tIRExpr(cas.expdLo);
                    Vns dataLo = tIRExpr(cas.dataLo);
                    if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
                        Vns expdHi = tIRExpr(cas.expdHi);
                        Vns dataHi = tIRExpr(cas.dataHi);
                        emu[cas.oldHi] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                        emu[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                        mem.Ist_Store(addr, dataLo);
                        mem.Ist_Store(addr + (dataLo.bitn >> 3), dataHi);
                    }
                    else {//single
                        emu[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                        mem.Ist_Store(addr, dataLo);
                    }
                    break;
                }
                case Ist_Exit: {
                    Vns guard = tIRExpr(s->Ist.Exit.guard).simplify();
                    std::vector<Vns> guard_result;
                    if (guard.real()) {
                        if ((UChar)guard & 1) {
                        Exit_guard_true:
                            vassert(s->Ist.Exit.jk == Ijk_Boring);
                            m_host_addr = (UChar*)s->Ist.Exit.dst->Ico.U64;
                            goto For_Begin;
                        };
                    }
                    else {
                        UInt eval_size = eval_all(guard_result, m_solv, guard);
                        vassert(eval_size <= 2);
                        if (eval_size == 0) { m_status = Death; goto EXIT; }
                        if (eval_size == 1) {
                            if (((UChar)guard_result[0].simplify()) & 1)
                                goto Exit_guard_true;
                        }
                        if (eval_size == 2) {
                            if (s->Ist.Exit.jk != Ijk_Boring) {
                                m_solv.add_assert(guard, False);
                            }
                            else {
                                vassert(s->Ist.Exit.jk == Ijk_Boring);
                                newBranch = mkState(s->Ist.Exit.dst->Ico.U64);
                                newBranch->m_solv.add_assert(guard);
                                m_status = Fork;
                            }
                        }
                    }
                    break;
                }
                case Ist_NoOp: break;
                case Ist_IMark: {
                    if (m_status == Fork) {
                        DState* prv = newBranch;
                        newBranch = mkState(s->Ist.IMark.addr);
                        newBranch->m_solv.add_assert(prv->m_solv.get_asserts()[0], False);
                        goto EXIT;
                    };
                    m_host_addr = (UChar*)s->Ist.IMark.addr;
                    break;
                };
                case Ist_AbiHint: { m_InvokStack.push(tIRExpr(s->Ist.AbiHint.nia), tIRExpr(s->Ist.AbiHint.base)); break; }
                case Ist_PutI: {
                    auto ix = tIRExpr(s->Ist.PutI.details->ix);
                    vassert(ix.real());
                    regs.Ist_Put(
                        s->Ist.PutI.details->descr->base + (((UInt)((s->Ist.PutI.details->bias + (int)(ix)))) % s->Ist.PutI.details->descr->nElems) * ty2length(s->Ist.PutI.details->descr->elemTy),
                        tIRExpr(s->Ist.PutI.details->data)
                    );
                    break;
                }
                case Ist_Dirty: {
                    getDirtyVexCtx();
                    IRDirty* dirty = s->Ist.Dirty.details;
                    Vns guard = tIRExpr(dirty->guard);
                    if (guard.symbolic()) {
                        VPANIC("auto guard = m_state.tIRExpr(dirty->guard); symbolic");
                    }
                    if (((UChar)guard) & 1) {
                        dirty_run(dirty);
                        if (dirty->tmp != IRTemp_INVALID) {
                            emu[dirty->tmp] = result(typeOfIRTemp(irsb->tyenv, dirty->tmp));
                        }
                    }

                    break;
                }
                case Ist_LoadG: {
                    IRLoadG* lg = s->Ist.LoadG.details;
                    auto guard = tIRExpr(lg->guard);
                    if (guard.real()) {
                        emu[lg->dst] = (((UChar)guard & 1)) ? ILGop(lg) : tIRExpr(lg->alt);
                    }
                    else {
                        emu[lg->dst] = ite(guard == 1, ILGop(lg), tIRExpr(lg->alt));
                    }
                    break;
                }
                case Ist_StoreG: {
                    IRStoreG* sg = s->Ist.StoreG.details;
                    auto guard = tIRExpr(sg->guard);
                    if (guard.real()) {
                        if ((UChar)guard)
                            mem.Ist_Store(tIRExpr(sg->addr), tIRExpr(sg->data));
                    }
                    else {
                        auto addr = tIRExpr(sg->addr);
                        auto data = tIRExpr(sg->data);
                        mem.Ist_Store(addr, ite(guard == 1, mem.Iex_Load(addr, (IRType)(data.bitn)), data));
                    }
                    break;
                }
                case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/ {
                    vex_printf("IR-");
                    ppIRMBusEvent(s->Ist.MBE.event);
                    break;
                }
                case Ist_LLSC:
                default: {
                    ppIRSB(irsb);
                    vex_printf("addr: %p what ppIRStmt %d\n", m_host_addr, s->tag);
                    VPANIC("what ppIRStmt");
                }
                }
#ifdef OUTPUT_STMTS
                vex_printf("\n");
#endif
            }

            switch (irsb->jumpkind) {
            case Ijk_Boring:        break;
            case Ijk_Call:          break;
            case Ijk_Ret: {
                m_InvokStack.pop();
                break;
            }
            default:
                goto Faild_EXIT;
            };

        Isb_next:
            Vns next = tIRExpr(irsb->next);
            if (m_status == Fork) {
                DState* prv = newBranch;
                Vns const& guard = prv->m_solv.get_asserts()[0];
                if (next.real()) {
                    newBranch = mkState(next);
                    newBranch->m_solv.add_assert(guard, False);
                }
                else {
                    std::vector<Vns> result;
                    UInt eval_size = eval_all(result, m_solv, next);
                    if (eval_size == 0) { m_status = Death; goto EXIT; }
                    else if (eval_size == 1) { m_host_addr = result[0].simplify(); }
                    else {
                        for (auto re : result) {
                            Addr64 GN = re.simplify();//guest next ip
                            newBranch = mkState(GN);
                            newBranch->m_solv.add_assert(guard, False);
                            newBranch->m_solv.add_assert_eq(next, re);
                        }
                    }
                }
                goto EXIT;
            }

            if (next.real()) {
                m_host_addr = next;
            }
            else {
                std::vector<Vns> result;
                UInt eval_size = eval_all(result, m_solv, next);
                if (eval_size == 0) { m_status = Death; goto EXIT; }
                else if (eval_size == 1) { m_host_addr = result[0].simplify(); }
                else {
                    for (auto re : result) {
                        Addr64 GN = re.simplify();//guest next ip
                        newBranch = mkState(GN);
                        newBranch->m_solv.add_assert_eq(next, re);
                    }
                    m_status = Fork;
                    goto EXIT;
                }
            }

        }
#ifdef OUTPUT_STMTS
        vex_printf("\n\n\n");
#endif
    EXIT:
        m_irtemp = nullptr;
        return;
    Faild_EXIT:
        m_irtemp = nullptr;
        set_status(Death);
    }

public:
    void start() {
        try {
            exec();
            if (status() == Dirty_ret) {
                return;
            }
            else {
                VPANIC("FGH");
            }

        }
        catch (Expt::ExceptionBase & error) {
            std::cout << "dirty err :: " << std::endl;
            switch ((Expt::ExceptionTag)error) {
            case Expt::GuestMem_read_err:
            case Expt::GuestMem_write_err: {
                std::cout << "Usage issues or simulation software problems.\nError message:" << std::endl;
                std::cout << error << std::endl;
                m_status = Death;
                break;
            }
            case Expt::IR_failure_exit: {
                std::cout << "Sorry This could be my design error. (BUG)\nError message:" << std::endl;
                std::cout << error << std::endl;
                exit(1);
            }
            case Expt::Solver_no_solution: {
                std::cout << " There is no solution to this problem. But this COULD BE my design error (BUG).\nError message:" << std::endl;
                std::cout << error << std::endl;
                exit(1);
            }
            };
        }
    }



    void compress(cmpr::CmprsContext<DState, State_Tag>& ctx);
};



template<typename ADDR>
class VexIRDirty :public DState {
    State<ADDR>& m_state;

public:
    VexIRDirty(State<ADDR>& state) :DState(state.info(), state.m_ctx, state.solv, state.mem), m_state(state) { }
    ~VexIRDirty(){  }

    virtual void     store_regs_to_mem(IRDirty* dirty) override { mem.store_regs_to_mem(m_guest_regs_map_addr, m_state.regs, dirty); }
    virtual void     put_regs_from_mem(IRDirty* dirty) override { mem.put_regs_from_mem(m_state.regs, dirty); }
    virtual Vns      base_tIRExpr(IRExpr* e) override { return m_state.tIRExpr(e); }

};


class DStateIRDirty :public DState {
    DState& m_state;

    ~DStateIRDirty() {  }

    virtual void     store_regs_to_mem(IRDirty* dirty) override { mem.store_regs_to_mem(m_guest_regs_map_addr, m_state.regs, dirty); }
    virtual void     put_regs_from_mem(IRDirty* dirty) override { mem.put_regs_from_mem(m_state.regs, dirty); }
    virtual Vns      base_tIRExpr(IRExpr* e) override { return m_state.tIRExpr(e); }
    virtual IRSB*    translate(
        /*MOD*/ VexTranslateArgs* vta,
        /*OUT*/ VexTranslateResult* res,
        /*OUT*/ VexRegisterUpdates* pxControl,
        Pap* pap
    ) override {
        return LibVEX_FrontEnd(vta, res, pxControl, pap);
    }
public:
    DStateIRDirty(DState& state) :DState(state.m_vex_info, state.m_ctx, state.m_solv, state.mem), m_state(state) { }
};

DState* mk_DStateIRDirty(DState *s){
    return new DStateIRDirty(*s);
}



typedef ULong(*Function_32_6)(UInt, UInt, UInt, UInt, UInt, UInt);
typedef ULong(*Function_32_5)(UInt, UInt, UInt, UInt, UInt);
typedef ULong(*Function_32_4)(UInt, UInt, UInt, UInt);
typedef ULong(*Function_32_3)(UInt, UInt, UInt);
typedef ULong(*Function_32_2)(UInt, UInt);
typedef ULong(*Function_32_1)(UInt);
typedef ULong(*Function_32_0)();

typedef ULong(*Function_64_6)(ULong, ULong, ULong, ULong, ULong, ULong);
typedef ULong(*Function_64_5)(ULong, ULong, ULong, ULong, ULong);
typedef ULong(*Function_64_4)(ULong, ULong, ULong, ULong);
typedef ULong(*Function_64_3)(ULong, ULong, ULong);
typedef ULong(*Function_64_2)(ULong, ULong);
typedef ULong(*Function_64_1)(ULong);
typedef ULong(*Function_64_0)();

typedef Vns(*Z3_Function6)(Vns&, Vns&, Vns&, Vns&, Vns&, Vns&);
typedef Vns(*Z3_Function5)(Vns&, Vns&, Vns&, Vns&, Vns&);
typedef Vns(*Z3_Function4)(Vns&, Vns&, Vns&, Vns&);
typedef Vns(*Z3_Function3)(Vns&, Vns&, Vns&);
typedef Vns(*Z3_Function2)(Vns&, Vns&);
typedef Vns(*Z3_Function1)(Vns&);

#define CDFCHECK(arg0)\
if (arg0.symbolic()) {\
    z3_mode = True;\
    if (!cptr) { return dirty_call(cee, exp_args, ty); };\
}

Vns DState::CCall(IRCallee* cee, IRExpr** exp_args, IRType ty)
{
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return Vns(m_ctx, ((Function_64_0)(cee->addr))(), bitn);

    void* cptr = funcDict(cee->addr);
    Vns arg0 = tIRExpr(exp_args[0]); CDFCHECK(arg0);
    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(cptr))(arg0) : Vns(m_ctx, ((Function_64_1)(cee->addr))(arg0), bitn);
    Vns arg1 = tIRExpr(exp_args[1]); CDFCHECK(arg1);
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(cptr))(arg0, arg1) : Vns(m_ctx, ((Function_64_2)(cee->addr))(arg0, arg1), bitn);
    Vns arg2 = tIRExpr(exp_args[2]); CDFCHECK(arg2);
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(cptr))(arg0, arg1, arg2) : Vns(m_ctx, ((Function_64_3)(cee->addr))(arg0, arg1, arg2), bitn);
    Vns arg3 = tIRExpr(exp_args[3]); CDFCHECK(arg3);
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(cptr))(arg0, arg1, arg2, arg3) : Vns(m_ctx, ((Function_64_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    Vns arg4 = tIRExpr(exp_args[4]); CDFCHECK(arg4);
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4) : Vns(m_ctx, ((Function_64_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    Vns arg5 = tIRExpr(exp_args[5]); CDFCHECK(arg5);
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5) : Vns(m_ctx, ((Function_64_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
    VPANIC("not support");
}

#undef CDFCHECK


Vns DState::tIRExpr(IRExpr* e)
{
    switch (e->tag) {
    case Iex_Get: { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
    case Iex_RdTmp: { return m_irtemp[e->Iex.RdTmp.tmp]; }
    case Iex_Unop: { return Kernel::T_Unop(m_ctx, e->Iex.Unop.op, tIRExpr(e->Iex.Unop.arg)); }
    case Iex_Binop: { return  Kernel::T_Binop(m_ctx, e->Iex.Binop.op, tIRExpr(e->Iex.Binop.arg1), tIRExpr(e->Iex.Binop.arg2)); }
    case Iex_Triop: { return  Kernel::T_Triop(m_ctx, e->Iex.Triop.details->op, tIRExpr(e->Iex.Triop.details->arg1), tIRExpr(e->Iex.Triop.details->arg2), tIRExpr(e->Iex.Triop.details->arg3)); }
    case Iex_Qop: { return  Kernel::T_Qop(m_ctx, e->Iex.Qop.details->op, tIRExpr(e->Iex.Qop.details->arg1), tIRExpr(e->Iex.Qop.details->arg2), tIRExpr(e->Iex.Qop.details->arg3), tIRExpr(e->Iex.Qop.details->arg4)); }
    case Iex_Load: { return mem.Iex_Load(tIRExpr(e->Iex.Load.addr), e->Iex.Get.ty); }
    case Iex_Const: { return Vns(m_ctx, e->Iex.Const.con); }
    case Iex_ITE: {
        Vns cond = tIRExpr(e->Iex.ITE.cond);
        return (cond.real()) ?
            ((UChar)cond & 0b1) ? tIRExpr(e->Iex.ITE.iftrue) : tIRExpr(e->Iex.ITE.iffalse)
            :
            Vns(m_ctx, Z3_mk_ite(m_ctx, cond.toZ3Bool(), tIRExpr(e->Iex.ITE.iftrue), tIRExpr(e->Iex.ITE.iffalse)));
    }
    case Iex_CCall: { return CCall(e->Iex.CCall.cee, e->Iex.CCall.args, e->Iex.CCall.retty); }
    case Iex_GetI: {
        auto ix = tIRExpr(e->Iex.GetI.ix);   /*  [e->Iex.GetI.ix, e->Iex.GetI.bias];  */
        assert(ix.real());
        return regs.Iex_Get(e->Iex.GetI.descr->base + (((UInt)(e->Iex.GetI.bias + (int)(ix))) % e->Iex.GetI.descr->nElems) * ty2length(e->Iex.GetI.descr->elemTy), e->Iex.GetI.descr->elemTy);
    };
    case Iex_GSPTR: {
        return Vns(m_ctx, (Addr64)getGSPTR());
    };
    case Iex_VECRET:
    case Iex_Binder:
    default:
        vex_printf("tIRExpr error:  %d", e->tag);
        VPANIC("not support");
    }
}




class DStateCmprsInterface {
    cmpr::CmprsContext<DState, State_Tag>& m_ctx;
    DState& m_state;
    cmpr::StateType m_type;
    Vns m_condition;
    static bool StateCompression(DState& a, DState const& next) {
        bool ret = a.m_InvokStack == next.m_InvokStack;// 压缩条件
        return ret && a.StateCompression(next);//支持扩展条件
    }

    static void StateCompressMkSymbol(DState& a, DState const& newState) {
        a.m_InvokStack = newState.m_InvokStack;// 使其满足压缩条件
        a.StateCompressMkSymbol(newState);//支持
    }

    std::vector<Vns> const& get_asserts() const { return m_state.m_solv.get_asserts(); };

public:
    DStateCmprsInterface(
        cmpr::CmprsContext<DState, State_Tag>& ctx,
        DState& self,
        cmpr::StateType type
    ) :
        m_ctx(ctx), m_state(self), m_type(type), m_condition(ctx, 0, 0)
    { };

    cmpr::CmprsContext<DState, State_Tag>& cctx() { return m_ctx; }
    cmpr::StateType type() { return m_type; };

    Vns const& get_assert() {
        if (!m_condition.bitn) {
            m_condition = cmpr::logic_and(get_asserts()).translate(m_ctx.ctx());
        }
        return m_condition;
    }

    void get_write_map(std::hash_map<Addr64, bool>& record) {
        if (m_state.regs.record) {
            for (auto offset : *m_state.regs.record) {
                record[offset];
            }
        }
        for (auto mcm : m_state.mem.change_map()) {
            vassert(mcm.second->record != NULL);
            for (auto offset : *(mcm.second->record)) {
                auto Address = mcm.first + offset;
                auto p = m_state.mem.getMemPage(Address);
                vassert(p);
                vassert(p->get_user() == m_state.mem.get_user());
                vassert(Address > REGISTER_LEN);
                record[Address];
            }
        }
    }

    auto& branch() { return m_state.branch; };

    cmpr::StateType tag(DState* son) {
        if (son->status() == Fork) {
            return cmpr::Fork_Node;
        };
        if (m_ctx.is_avoid(son->status())) {
            return cmpr::Avoid_Node;
        };
        if (son->get_cpu_ip() == m_ctx.get_target_addr()) {
            return static_cast<cmpr::StateType>(get_group_id(son));
        }
        return cmpr::Survive_Node;
    };

    Int get_group_id(DState* s) {
        UInt group_count = 0;
        for (auto gs : m_ctx.group()) {
            if (StateCompression(*gs, *s)) {
                return group_count;
            }
            group_count++;
        }
        m_ctx.group().emplace_back(s);
        return group_count;
    }

    void del_obj() {
        delete& m_state;
    }

    Vns mem_Load(Addr64 addr) {
        return m_state.mem.Iex_Load<Ity_I64>(addr).translate(m_ctx.ctx());
    }

    Vns reg_Get(UInt offset) {
        return m_state.regs.Iex_Get<Ity_I64>(offset).translate(m_ctx.ctx());
    }

    Vns read(Addr64 addr) {
        if (addr < REGISTER_LEN) {
            return reg_Get(addr);
        }
        else {
            return mem_Load(addr);
        }
    }

    DStateCmprsInterface* mk(DState* son, cmpr::StateType tag) {
        //实际上少于4个case intel编译器会转为if
        switch (tag) {
        case cmpr::Fork_Node:return new cmpr::CmprsFork<DStateCmprsInterface>(m_ctx, *son);
        case cmpr::Avoid_Node:return new cmpr::CmprsAvoid<DStateCmprsInterface>(m_ctx, *son);
        case cmpr::Survive_Node:return new cmpr::CmprsSurvive<DStateCmprsInterface>(m_ctx, *son);
        default:return new cmpr::CmprsTarget<DStateCmprsInterface>(m_ctx, *son, tag);
        };

    }

    virtual bool has_survive() { return false; }
    virtual cmpr::CmprsFork<DStateCmprsInterface>& get_fork_node() { VPANIC("???"); }
    virtual cmpr::CmprsTarget<DStateCmprsInterface>& get_target_node() { VPANIC("???"); }
    virtual ~DStateCmprsInterface() {};

};

void DState::compress(cmpr::CmprsContext<DState, State_Tag>& ctx)
{
    cmpr::Compress<DStateCmprsInterface, DState, State_Tag> cmp(ctx, *this);
    if (!ctx.group().size()) {
        return;
    }
    else if (ctx.group().size() > 1 || (ctx.group().size() == 1 && cmp.has_survive())) {

        for (cmpr::Compress<DStateCmprsInterface, DState, State_Tag>::Iterator::StateRes state : cmp) {
            DState* nbranch = (DState*)mkState(ctx.get_target_addr());
            Vns condition = state.conditions().translate(*nbranch);
#ifdef  PPCMPR
            printf("%s\n", Z3_ast_to_string(condition, condition));
#endif //  _DEBUG
            nbranch->m_solv.add_assert(condition);
            std::hash_map<Addr64, cmpr::GPMana> const& cm = state.changes();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator itor = cm.begin();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator end = cm.end();

            for (; itor != end; itor++) {
                Addr64 addr = itor->first;
                Vns value = itor->second.get().translate(*nbranch);
#ifdef  PPCMPR
                printf("%p : {  %s  }\n", itor->first, Z3_ast_to_string(value, value));
#endif //  _DEBUG
                if (addr > REGISTER_LEN) {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    nbranch->mem.Ist_Store(addr, value);
                }
                else {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    nbranch->regs.Ist_Put(addr, value);
                }
            }
        }
    }
    else {
        for (cmpr::Compress<DStateCmprsInterface, DState, State_Tag>::Iterator::StateRes state : cmp) {
            Vns condition = state.conditions();
#ifdef  PPCMPR
            printf("%s\n", Z3_ast_to_string(condition, condition));
#endif //  _DEBUG
            m_solv.add_assert(condition);
            std::hash_map<Addr64, cmpr::GPMana> const& cm = state.changes();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator itor = cm.begin();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator end = cm.end();
            cmp.clear_nodes();
            for (; itor != end; itor++) {
                Addr64 addr = itor->first;
                Vns value = itor->second.get();
#ifdef  PPCMPR
                printf("%p : {  %s  }\n", itor->first, Z3_ast_to_string(value, value));
#endif //  _DEBUG
                if (addr > REGISTER_LEN) {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    mem.Ist_Store(addr, value);
                }
                else {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    regs.Ist_Put(addr, value);
                }
            }
        }
        m_host_addr = (UChar*)ctx.get_target_addr();
        set_status(NewState);
    }
}


template<typename ADDR>
DirtyCtx dirty_context(State<ADDR>* s) {
    return (DirtyCtx)new VexIRDirty<ADDR>(*s);
}
template<typename ADDR>
Addr64 dirty_get_gsptr(DirtyCtx dctx) {
    return ((VexIRDirty<ADDR>*)dctx)->getGSPTR();
}
template<typename ADDR>
void dirty_context_del(DirtyCtx dctx) {
    delete ((VexIRDirty<ADDR>*)dctx);
}

template<typename ADDR>
void dirty_ccall(DirtyCtx dctx, IRCallee* cee, IRExpr** args) {
    VexIRDirty<ADDR>* d = (VexIRDirty<ADDR>*)dctx;
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    vexSetAllocModeTEMP_and_save_curr();
    d->init_param(cee, args);
    d->start();
}

template<typename ADDR>
void dirty_run(DirtyCtx dctx, IRDirty* dirty) {
    VexIRDirty<ADDR>* d = (VexIRDirty<ADDR>*)dctx;
    d->store_regs_to_mem(dirty);
    dirty_ccall<ADDR>(dctx, dirty->cee, dirty->args);
    d->put_regs_from_mem(dirty);
}

template<typename ADDR>
Vns dirty_result(DirtyCtx dctx, IRType rty) {
    VexIRDirty<ADDR>* d = (VexIRDirty<ADDR>*)dctx;
    return d->result(rty);
}

template DirtyCtx dirty_context(State<Addr32>* s);
template DirtyCtx dirty_context(State<Addr64>* s);
template Addr64 dirty_get_gsptr<Addr32>(DirtyCtx dctx);
template Addr64 dirty_get_gsptr<Addr64>(DirtyCtx dctx);
template void dirty_run<Addr32>(DirtyCtx dctx, IRDirty* dirty);
template void dirty_run<Addr64>(DirtyCtx dctx, IRDirty* dirty);
template void dirty_context_del<Addr32>(DirtyCtx dctx);
template void dirty_context_del<Addr64>(DirtyCtx dctx);
template void dirty_ccall<Addr32>(DirtyCtx dctx, IRCallee* cee, IRExpr** args);
template void dirty_ccall<Addr64>(DirtyCtx dctx, IRCallee* cee, IRExpr** args);
template Vns dirty_result<Addr32>(DirtyCtx dctx, IRType rty);
template Vns dirty_result<Addr64>(DirtyCtx dctx, IRType rty);



