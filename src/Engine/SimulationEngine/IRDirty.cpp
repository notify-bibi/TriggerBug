
#include "IRDirty.hpp"

static thread_local UChar  dirty_dirty_ir_temp_trunk[MAX_IRTEMP * sizeof(Vns)];
#define dirty_ir_temp ((Vns*)dirty_dirty_ir_temp_trunk)

#ifdef _DEBUG
//#define OUTPUT_STMTS
#endif

extern "C" void vexSetAllocModeTEMP_and_save_curr(void);
static IRSB* LibVEX_FrontEnd_coexistence( /*MOD*/ VexTranslateArgs* vta,
    /*OUT*/ VexTranslateResult* res,
    /*OUT*/ VexRegisterUpdates* pxControl,
    Pap* pap);


class DMEM : public MEM<Addr64> {
    Addr64 m_stack_reservve_size;
    Addr64 m_stack_addr;
    Addr64 m_guest_regs_map_addr;
    bool m_front;

public:
    template<typename ADDR>
    DMEM(TRsolver& s, TRcontext& ctx, MEM<ADDR>& mem, bool front, Bool _need_record) : MEM(s, ctx, mem.CR3, mem.user, _need_record),
        m_front(front),
        m_stack_reservve_size(0),
        m_stack_addr(0),
        m_guest_regs_map_addr(0)
    {
        vassert(REGISTER_LEN < 0x1000);
    };

    //FORK
    DMEM(solver& so, TRcontext& ctx, DMEM& father_mem, Bool _need_record): MEM(so, ctx, father_mem, _need_record),
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
           CR3 = nullptr;
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
DState* mk_DStateIRDirty(DState* s);

class DState :public Vex_Info {
    template <typename xx> friend class VexIRDirty;
    friend class DStateIRDirty;
    DState* m_base;
    Pap m_pap;
    bool m_front;
    TRcontext _m_z3_ctx;
    TRsolver  _m_z3_solv;
    TRcontext& m_ctx;
    TRsolver& m_solv;
    Register<REGISTER_LEN>  regs;
    DMEM                    mem;

    bool    m_dirty_vex_mode = false;
    DState* m_dctx = nullptr;
    Addr64 m_stack_reservve_size = 0x1000;
    Addr64 m_stack_addr;
    Addr64 m_guest_regs_map_addr;

    Addr64 vex_ret_addr = 0x1ull;// Dont patch it

    VexTranslateArgs m_vta_chunk;
    VexGuestExtents m_vge_chunk;
    BranchManager<DState> branch;
    State_Tag   m_status;
    InvocationStack<Addr64>   m_InvokStack;
    UChar* m_host_addr;
    UChar* m_host_ep;
    Vns*   m_irtemp;
    //fork
    DState(DState& fork) :
        m_base(&fork),
        _m_z3_ctx(),
        _m_z3_solv(_m_z3_ctx, fork.m_solv, z3::solver::translate{}),
        m_ctx(_m_z3_ctx),
        m_solv(_m_z3_solv),
        regs(_m_z3_ctx, true),
        mem(_m_z3_solv, _m_z3_ctx, fork.mem, true),
        m_front(false),
        m_stack_addr(mem.find_block_reverse(fork.m_stack_addr - 0x1000, m_stack_reservve_size)),
        m_guest_regs_map_addr(mem.find_block_forward(fork.m_guest_regs_map_addr + 0x1000, REGISTER_LEN)),
        vex_ret_addr(fork.vex_ret_addr + 1),
        branch(*this, fork.branch),
        m_status(NewState),
        m_host_addr(nullptr),
        m_host_ep(nullptr)
    {
        m_pap.state = nullptr;
        m_pap.n_page_mem = nullptr;
        m_pap.guest_max_insns = 100;
        mem.map(m_stack_addr, m_stack_reservve_size);
        mem.map(m_guest_regs_map_addr, 1000);
        mem.set_clear(m_stack_reservve_size, m_stack_addr, m_guest_regs_map_addr);
        init_vta_chunk(m_vta_chunk, m_vge_chunk, VexArchAMD64, 0);
    };

    //fork
    DState(DState& fork, Addr64 oep) :DState(fork) {
        m_host_ep = (UChar*)oep;
        m_host_addr = (UChar*)oep;
    }
public:
    //dirty call
    template<typename ADDR>
    DState(TRcontext& ctx, TRsolver&solver, MEM<ADDR>& memory) :
        m_base(nullptr),
        _m_z3_ctx(),
        _m_z3_solv(ctx),
        m_ctx(ctx),
        m_solv(solver),
        regs(ctx, true),
        mem(solver, ctx, memory, true, true),
        m_front(true),
        m_stack_addr(memory.find_block_reverse((ADDR)0 - 0x10000, m_stack_reservve_size)),
        m_guest_regs_map_addr(memory.find_block_forward(0x1000, REGISTER_LEN)),
        vex_ret_addr(1),
        branch(*this),
        m_status(NewState),
        m_host_addr(nullptr),
        m_host_ep(nullptr)

    {
        m_pap.state = nullptr;
        m_pap.n_page_mem = nullptr;
        m_pap.guest_max_insns = 100;
        mem.map(m_stack_addr, m_stack_reservve_size);
        mem.map(m_guest_regs_map_addr, 1000);
        mem.set_clear(m_stack_reservve_size, m_stack_addr, m_guest_regs_map_addr);
        init_vta_chunk(m_vta_chunk, m_vge_chunk, VexArchAMD64, 0);
    };


    ~DState() {
        if (m_dirty_vex_mode) {
            delete ((DState*)m_dctx);
        }
    };

    inline State_Tag    status() { return m_status; }
    inline void         set_status(State_Tag t) { m_status = t; };
    Vns                 CCall(IRCallee* cee, IRExpr** exp_args, IRType ty);
    Vns                 tIRExpr(IRExpr* e);
    IRSB*               translate(UChar* Host_code);
    Vns                 result(IRType ty) { return regs.Iex_Get(AMD64_IR_OFFSET::RAX, ty); }
    inline Addr64       getGSPTR() { return m_guest_regs_map_addr; }
    DState*             mkState(Addr64 ges) { return new DState(*this, ges); }
    void                set_ip(UChar* Haddr) { m_host_addr = Haddr; };
    inline operator     TRcontext& (){ return m_ctx; }

    virtual void     store_regs_to_mem(IRDirty* dirty) { mem.store_regs_to_mem(m_guest_regs_map_addr, regs, dirty); }
    virtual void     put_regs_from_mem(IRDirty* dirty) { mem.put_regs_from_mem(regs, dirty); }
    virtual Vns      base_tIRExpr(IRExpr* e) { return m_base->tIRExpr(e).translate(m_ctx); }
    virtual IRSB*    translate() {
        m_pap.start_swap = 2;
        m_vta_chunk.guest_bytes = m_host_addr;
        m_vta_chunk.guest_bytes_addr = (Addr64)(m_host_addr);
        VexRegisterUpdates pxControl;
        VexTranslateResult res;
        return LibVEX_FrontEnd_coexistence(&m_vta_chunk, &res, &pxControl, &m_pap);
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

    void init_irTemp()
    {
        for (int j = 0; j < MAX_IRTEMP; j++) {
            m_irtemp[j].Vns::Vns(m_ctx, 0);
        }
    }

    void clear_irTemp()
    {
        for (int j = 0; j < MAX_IRTEMP; j++) {
            m_irtemp[j].~Vns();
        }
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
        m_irtemp = dirty_ir_temp;
        init_irTemp();
        DState* newBranch = nullptr;
        set_status(Running);

        while (true) {
            if (reinterpret_cast<Addr64>(m_host_addr) == vex_ret_addr) {
                Addr64 stack_ret = m_stack_addr + m_stack_reservve_size - 0x8ull * 6;
                Vns rsp = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RSP);
                if (rsp.real()) {
                    vassert((ULong)rsp == stack_ret);
                    break;
                }
                VPANIC("????");
            }
        For_Begin:
            IRSB* irsb = translate();
            IRStmt* s = irsb->stmts[0];
            for (UInt stmtn = 0; stmtn < irsb->stmts_used;
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
                    m_irtemp[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data);
#ifdef OUTPUT_STMTS
                    std::cout << m_irtemp[s->Ist.WrTmp.tmp];
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
                        m_irtemp[cas.oldHi] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                        m_irtemp[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                        mem.Ist_Store(addr, dataLo);
                        mem.Ist_Store(addr + (dataLo.bitn >> 3), dataHi);
                    }
                    else {//single
                        m_irtemp[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
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
                            ir_temp[dirty->tmp] = result(typeOfIRTemp(irsb->tyenv, dirty->tmp));
                        }
                    }

                    break;
                }
                case Ist_LoadG: {
                    IRLoadG* lg = s->Ist.LoadG.details;
                    auto guard = tIRExpr(lg->guard);
                    if (guard.real()) {
                        m_irtemp[lg->dst] = (((UChar)guard & 1)) ? ILGop(lg) : tIRExpr(lg->alt);
                    }
                    else {
                        m_irtemp[lg->dst] = ite(guard == 1, ILGop(lg), tIRExpr(lg->alt));
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
        clear_irTemp();
        set_status(Dirty_ret);
        return;
    Faild_EXIT:
        clear_irTemp();
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
};



class TRsolver;
template<typename ADDR>
class VexIRDirty :public DState {
    State<ADDR>& m_state;

public:
    VexIRDirty(State<ADDR>& state) :DState(state.m_ctx, state.solv, state.mem), m_state(state) { }
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
    virtual IRSB*    translate() override {
        m_pap.start_swap = 2;
        m_vta_chunk.guest_bytes = m_host_addr;
        m_vta_chunk.guest_bytes_addr = (Addr64)(m_host_addr);
        VexRegisterUpdates pxControl;
        VexTranslateResult res;
        return LibVEX_FrontEnd(&m_vta_chunk, &res, &pxControl, &m_pap);
    }
public:
    DStateIRDirty(DState& state) :DState(state.m_ctx, state.m_solv, state.mem), m_state(state) { }
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







extern "C" {
#include "libvex.h"
#include "libvex_emnote.h"
#include "libvex_guest_x86.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_arm.h"
#include "libvex_guest_arm64.h"
#include "libvex_guest_ppc32.h"
#include "libvex_guest_ppc64.h"
#include "libvex_guest_s390x.h"
#include "libvex_guest_mips32.h"
#include "libvex_guest_mips64.h"

#include "main_globals.h"
#include "main_util.h"
#include "host_generic_regs.h"
#include "ir_opt.h"

#include "host_x86_defs.h"
#include "host_amd64_defs.h"
#include "host_ppc_defs.h"
#include "host_arm_defs.h"
#include "host_arm64_defs.h"
#include "host_s390_defs.h"
#include "host_mips_defs.h"

#include "guest_generic_bb_to_IR.h"
#include "guest_x86_defs.h"
#include "guest_amd64_defs.h"
#include "guest_arm_defs.h"
#include "guest_arm64_defs.h"
#include "guest_ppc_defs.h"
#include "guest_s390_defs.h"
#include "guest_mips_defs.h"

#include "host_generic_simd128.h"
};


extern "C" void vexSetAllocMode(VexAllocMode m);

#define NULL nullptr

#if defined(VGA_x86) || defined(VEXMULTIARCH)
#define X86FN(f) f
#define X86ST(f) f
#else
#define X86FN(f) NULL
#define X86ST(f) vassert(0)
#endif

#if defined(VGA_amd64) || defined(VEXMULTIARCH)
#define AMD64FN(f) f
#define AMD64ST(f) f
#else
#define AMD64FN(f) NULL
#define AMD64ST(f) vassert(0)
#endif

#if defined(VGA_ppc32) || defined(VEXMULTIARCH)
#define PPC32FN(f) f
#define PPC32ST(f) f
#else
#define PPC32FN(f) NULL
#define PPC32ST(f) vassert(0)
#endif

#if defined(VGA_ppc64be) || defined(VGA_ppc64le) || defined(VEXMULTIARCH)
#define PPC64FN(f) f
#define PPC64ST(f) f
#else
#define PPC64FN(f) NULL
#define PPC64ST(f) vassert(0)
#endif

#if defined(VGA_s390x) || defined(VEXMULTIARCH)
#define S390FN(f) f
#define S390ST(f) f
#else
#define S390FN(f) NULL
#define S390ST(f) vassert(0)
#endif

#if defined(VGA_arm) || defined(VEXMULTIARCH)
#define ARMFN(f) f
#define ARMST(f) f
#else
#define ARMFN(f) NULL
#define ARMST(f) vassert(0)
#endif

#if defined(VGA_arm64) || defined(VEXMULTIARCH)
#define ARM64FN(f) f
#define ARM64ST(f) f
#else
#define ARM64FN(f) NULL
#define ARM64ST(f) vassert(0)
#endif

#if defined(VGA_mips32) || defined(VEXMULTIARCH)
#define MIPS32FN(f) f
#define MIPS32ST(f) f
#else
#define MIPS32FN(f) NULL
#define MIPS32ST(f) vassert(0)
#endif

#if defined(VGA_mips64) || defined(VEXMULTIARCH)
#define MIPS64FN(f) f
#define MIPS64ST(f) f
#else
#define MIPS64FN(f) NULL
#define MIPS64ST(f) vassert(0)
#endif

static inline IRType arch_word_size(VexArch arch) {
    switch (arch) {
    case VexArchX86:
    case VexArchARM:
    case VexArchMIPS32:
    case VexArchPPC32:
        return Ity_I32;

    case VexArchAMD64:
    case VexArchARM64:
    case VexArchMIPS64:
    case VexArchPPC64:
    case VexArchS390X:
        return Ity_I64;

    default:
        vex_printf("Fatal: unknown arch in arch_word_size\n");
        vassert(0);
    }
}


UInt getSP(VexArch arch) {
    switch (arch) {
    case VexArchX86:return offsetof(VexGuestX86State, guest_ESP);
    case VexArchAMD64:return offsetof(VexGuestAMD64State, guest_RSP);
    case VexArchARM:return offsetof(VexGuestARMState, guest_R13);
    case VexArchARM64:return offsetof(VexGuestARM64State, guest_XSP);
    case VexArchPPC32:return offsetof(VexGuestPPC32State, guest_GPR1);
    case VexArchPPC64:return offsetof(VexGuestPPC64State, guest_GPR1);
    case VexArchS390X:return offsetof(VexGuestS390XState, guest_r15);
    case VexArchMIPS32:return offsetof(VexGuestMIPS32State, guest_r29);
    case VexArchMIPS64:return offsetof(VexGuestPPC64State, guest_GPR1);
    default:
        VPANIC("Invalid arch in setSP.\n");
        break;
    }
}



IRSB* LibVEX_FrontEnd_coexistence( /*MOD*/ VexTranslateArgs* vta,
    /*OUT*/ VexTranslateResult* res,
    /*OUT*/ VexRegisterUpdates* pxControl,
    Pap* pap)
{
    IRExpr* (*specHelper)   (const HChar*, IRExpr**, IRStmt**, Int);
    Bool(*preciseMemExnsFn) (Int, Int, VexRegisterUpdates);
    DisOneInstrFn disInstrFn;

    VexGuestLayout* guest_layout;
    IRSB* irsb;
    Int             i;
    Int             offB_CMSTART, offB_CMLEN, offB_GUEST_IP, szB_GUEST_IP;
    IRType          guest_word_type;
    IRType          host_word_type;

    guest_layout = NULL;
    specHelper = NULL;
    disInstrFn = NULL;
    preciseMemExnsFn = NULL;
    guest_word_type = arch_word_size(vta->arch_guest);
    host_word_type = arch_word_size(vta->arch_host);
    offB_CMSTART = 0;
    offB_CMLEN = 0;
    offB_GUEST_IP = 0;
    szB_GUEST_IP = 0;

    vassert(vex_initdone);
    vassert(vta->needs_self_check != NULL);
    vassert(vta->disp_cp_xassisted != NULL);
    /* Both the chainers and the indir are either NULL or non-NULL. */
    if (vta->disp_cp_chain_me_to_slowEP != NULL) {
        vassert(vta->disp_cp_chain_me_to_fastEP != NULL);
        vassert(vta->disp_cp_xindir != NULL);
    }
    else {
        vassert(vta->disp_cp_chain_me_to_fastEP == NULL);
        vassert(vta->disp_cp_xindir == NULL);
    }

    vexTEMP_clear();
    vexAllocSanityCheck();

    vex_traceflags = vta->traceflags;

    /* KLUDGE: export hwcaps. */
    if (vta->arch_host == VexArchS390X) {
        s390_host_hwcaps = vta->archinfo_host.hwcaps;
    }

    /* First off, check that the guest and host insn sets
       are supported. */

    switch (vta->arch_guest) {

    case VexArchX86:
        preciseMemExnsFn
            = X86FN(guest_x86_state_requires_precise_mem_exns);
        disInstrFn = X86FN(disInstr_X86);
        specHelper = X86FN(guest_x86_spechelper);
        guest_layout = X86FN(&x86guest_layout);
        offB_CMSTART = offsetof(VexGuestX86State, guest_CMSTART);
        offB_CMLEN = offsetof(VexGuestX86State, guest_CMLEN);
        offB_GUEST_IP = offsetof(VexGuestX86State, guest_EIP);
        szB_GUEST_IP = sizeof(((VexGuestX86State*)0)->guest_EIP);
        vassert(vta->archinfo_guest.endness == VexEndnessLE);
        vassert(0 == sizeof(VexGuestX86State) % LibVEX_GUEST_STATE_ALIGN);
        vassert(sizeof(((VexGuestX86State*)0)->guest_CMSTART) == 4);
        vassert(sizeof(((VexGuestX86State*)0)->guest_CMLEN) == 4);
        vassert(sizeof(((VexGuestX86State*)0)->guest_NRADDR) == 4);
        break;

    case VexArchAMD64:
        preciseMemExnsFn
            = AMD64FN(guest_amd64_state_requires_precise_mem_exns);
        disInstrFn = AMD64FN(disInstr_AMD64);
        specHelper = AMD64FN(guest_amd64_spechelper);
        guest_layout = AMD64FN(&amd64guest_layout);
        offB_CMSTART = offsetof(VexGuestAMD64State, guest_CMSTART);
        offB_CMLEN = offsetof(VexGuestAMD64State, guest_CMLEN);
        offB_GUEST_IP = offsetof(VexGuestAMD64State, guest_RIP);
        szB_GUEST_IP = sizeof(((VexGuestAMD64State*)0)->guest_RIP);
        vassert(vta->archinfo_guest.endness == VexEndnessLE);
        vassert(0 == sizeof(VexGuestAMD64State) % LibVEX_GUEST_STATE_ALIGN);
        vassert(sizeof(((VexGuestAMD64State*)0)->guest_CMSTART) == 8);
        vassert(sizeof(((VexGuestAMD64State*)0)->guest_CMLEN) == 8);
        vassert(sizeof(((VexGuestAMD64State*)0)->guest_NRADDR) == 8);
        break;

    case VexArchPPC32:
        preciseMemExnsFn
            = PPC32FN(guest_ppc32_state_requires_precise_mem_exns);
        disInstrFn = PPC32FN(disInstr_PPC);
        specHelper = PPC32FN(guest_ppc32_spechelper);
        guest_layout = PPC32FN(&ppc32Guest_layout);
        offB_CMSTART = offsetof(VexGuestPPC32State, guest_CMSTART);
        offB_CMLEN = offsetof(VexGuestPPC32State, guest_CMLEN);
        offB_GUEST_IP = offsetof(VexGuestPPC32State, guest_CIA);
        szB_GUEST_IP = sizeof(((VexGuestPPC32State*)0)->guest_CIA);
        vassert(vta->archinfo_guest.endness == VexEndnessBE);
        vassert(0 == sizeof(VexGuestPPC32State) % LibVEX_GUEST_STATE_ALIGN);
        vassert(sizeof(((VexGuestPPC32State*)0)->guest_CMSTART) == 4);
        vassert(sizeof(((VexGuestPPC32State*)0)->guest_CMLEN) == 4);
        vassert(sizeof(((VexGuestPPC32State*)0)->guest_NRADDR) == 4);
        break;

    case VexArchPPC64:
        preciseMemExnsFn
            = PPC64FN(guest_ppc64_state_requires_precise_mem_exns);
        disInstrFn = PPC64FN(disInstr_PPC);
        specHelper = PPC64FN(guest_ppc64_spechelper);
        guest_layout = PPC64FN(&ppc64Guest_layout);
        offB_CMSTART = offsetof(VexGuestPPC64State, guest_CMSTART);
        offB_CMLEN = offsetof(VexGuestPPC64State, guest_CMLEN);
        offB_GUEST_IP = offsetof(VexGuestPPC64State, guest_CIA);
        szB_GUEST_IP = sizeof(((VexGuestPPC64State*)0)->guest_CIA);
        vassert(vta->archinfo_guest.endness == VexEndnessBE ||
            vta->archinfo_guest.endness == VexEndnessLE);
        vassert(0 == sizeof(VexGuestPPC64State) % LibVEX_GUEST_STATE_ALIGN);
        vassert(sizeof(((VexGuestPPC64State*)0)->guest_CMSTART) == 8);
        vassert(sizeof(((VexGuestPPC64State*)0)->guest_CMLEN) == 8);
        vassert(sizeof(((VexGuestPPC64State*)0)->guest_NRADDR) == 8);
        vassert(sizeof(((VexGuestPPC64State*)0)->guest_NRADDR_GPR2) == 8);
        break;

    case VexArchS390X:
        preciseMemExnsFn
            = S390FN(guest_s390x_state_requires_precise_mem_exns);
        disInstrFn = S390FN(disInstr_S390);
        specHelper = S390FN(guest_s390x_spechelper);
        guest_layout = S390FN(&s390xGuest_layout);
        offB_CMSTART = offsetof(VexGuestS390XState, guest_CMSTART);
        offB_CMLEN = offsetof(VexGuestS390XState, guest_CMLEN);
        offB_GUEST_IP = offsetof(VexGuestS390XState, guest_IA);
        szB_GUEST_IP = sizeof(((VexGuestS390XState*)0)->guest_IA);
        vassert(vta->archinfo_guest.endness == VexEndnessBE);
        vassert(0 == sizeof(VexGuestS390XState) % LibVEX_GUEST_STATE_ALIGN);
        vassert(sizeof(((VexGuestS390XState*)0)->guest_CMSTART) == 8);
        vassert(sizeof(((VexGuestS390XState*)0)->guest_CMLEN) == 8);
        vassert(sizeof(((VexGuestS390XState*)0)->guest_NRADDR) == 8);
        break;

    case VexArchARM:
        preciseMemExnsFn
            = ARMFN(guest_arm_state_requires_precise_mem_exns);
        disInstrFn = ARMFN(disInstr_ARM);
        specHelper = ARMFN(guest_arm_spechelper);
        guest_layout = ARMFN(&armGuest_layout);
        offB_CMSTART = offsetof(VexGuestARMState, guest_CMSTART);
        offB_CMLEN = offsetof(VexGuestARMState, guest_CMLEN);
        offB_GUEST_IP = offsetof(VexGuestARMState, guest_R15T);
        szB_GUEST_IP = sizeof(((VexGuestARMState*)0)->guest_R15T);
        vassert(vta->archinfo_guest.endness == VexEndnessLE);
        vassert(0 == sizeof(VexGuestARMState) % LibVEX_GUEST_STATE_ALIGN);
        vassert(sizeof(((VexGuestARMState*)0)->guest_CMSTART) == 4);
        vassert(sizeof(((VexGuestARMState*)0)->guest_CMLEN) == 4);
        vassert(sizeof(((VexGuestARMState*)0)->guest_NRADDR) == 4);
        break;

    case VexArchARM64:
        preciseMemExnsFn
            = ARM64FN(guest_arm64_state_requires_precise_mem_exns);
        disInstrFn = ARM64FN(disInstr_ARM64);
        specHelper = ARM64FN(guest_arm64_spechelper);
        guest_layout = ARM64FN(&arm64Guest_layout);
        offB_CMSTART = offsetof(VexGuestARM64State, guest_CMSTART);
        offB_CMLEN = offsetof(VexGuestARM64State, guest_CMLEN);
        offB_GUEST_IP = offsetof(VexGuestARM64State, guest_PC);
        szB_GUEST_IP = sizeof(((VexGuestARM64State*)0)->guest_PC);
        vassert(vta->archinfo_guest.endness == VexEndnessLE);
        vassert(0 == sizeof(VexGuestARM64State) % LibVEX_GUEST_STATE_ALIGN);
        vassert(sizeof(((VexGuestARM64State*)0)->guest_CMSTART) == 8);
        vassert(sizeof(((VexGuestARM64State*)0)->guest_CMLEN) == 8);
        vassert(sizeof(((VexGuestARM64State*)0)->guest_NRADDR) == 8);
        break;

    case VexArchMIPS32:
        preciseMemExnsFn
            = MIPS32FN(guest_mips32_state_requires_precise_mem_exns);
        disInstrFn = MIPS32FN(disInstr_MIPS);
        specHelper = MIPS32FN(guest_mips32_spechelper);
        guest_layout = MIPS32FN(&mips32Guest_layout);
        offB_CMSTART = offsetof(VexGuestMIPS32State, guest_CMSTART);
        offB_CMLEN = offsetof(VexGuestMIPS32State, guest_CMLEN);
        offB_GUEST_IP = offsetof(VexGuestMIPS32State, guest_PC);
        szB_GUEST_IP = sizeof(((VexGuestMIPS32State*)0)->guest_PC);
        vassert(vta->archinfo_guest.endness == VexEndnessLE
            || vta->archinfo_guest.endness == VexEndnessBE);
        vassert(0 == sizeof(VexGuestMIPS32State) % LibVEX_GUEST_STATE_ALIGN);
        vassert(sizeof(((VexGuestMIPS32State*)0)->guest_CMSTART) == 4);
        vassert(sizeof(((VexGuestMIPS32State*)0)->guest_CMLEN) == 4);
        vassert(sizeof(((VexGuestMIPS32State*)0)->guest_NRADDR) == 4);
        break;

    case VexArchMIPS64:
        preciseMemExnsFn
            = MIPS64FN(guest_mips64_state_requires_precise_mem_exns);
        disInstrFn = MIPS64FN(disInstr_MIPS);
        specHelper = MIPS64FN(guest_mips64_spechelper);
        guest_layout = MIPS64FN(&mips64Guest_layout);
        offB_CMSTART = offsetof(VexGuestMIPS64State, guest_CMSTART);
        offB_CMLEN = offsetof(VexGuestMIPS64State, guest_CMLEN);
        offB_GUEST_IP = offsetof(VexGuestMIPS64State, guest_PC);
        szB_GUEST_IP = sizeof(((VexGuestMIPS64State*)0)->guest_PC);
        vassert(vta->archinfo_guest.endness == VexEndnessLE
            || vta->archinfo_guest.endness == VexEndnessBE);
        vassert(0 == sizeof(VexGuestMIPS64State) % LibVEX_GUEST_STATE_ALIGN);
        vassert(sizeof(((VexGuestMIPS64State*)0)->guest_CMSTART) == 8);
        vassert(sizeof(((VexGuestMIPS64State*)0)->guest_CMLEN) == 8);
        vassert(sizeof(((VexGuestMIPS64State*)0)->guest_NRADDR) == 8);
        break;

    default:
        vpanic("LibVEX_Translate: unsupported guest insn set");
    }


    res->status = VexTranslateResult::VexTransOK;
    res->n_sc_extents = 0;
    res->offs_profInc = -1;
    res->n_guest_instrs = 0;

#ifndef VEXMULTIARCH
    /* yet more sanity checks ... */
    if (vta->arch_guest == vta->arch_host) {
        /* doesn't necessarily have to be true, but if it isn't it means
           we are simulating one flavour of an architecture a different
           flavour of the same architecture, which is pretty strange. */
        vassert(vta->archinfo_guest.hwcaps == vta->archinfo_host.hwcaps);
        /* ditto */
        vassert(vta->archinfo_guest.endness == vta->archinfo_host.endness);
    }
#endif

    vexAllocSanityCheck();

    if (vex_traceflags & VEX_TRACE_FE)
        vex_printf("\n------------------------"
            " Front end "
            "------------------------\n\n");

    *pxControl = vex_control.iropt_register_updates_default;
    vassert(*pxControl >= VexRegUpdSpAtMemAccess
        && *pxControl <= VexRegUpdAllregsAtEachInsn);

    irsb = bb_to_IR(vta->guest_extents,
        &res->n_sc_extents,
        &res->n_guest_instrs,
        pxControl,
        vta->callback_opaque,
        disInstrFn,
        vta->guest_bytes,
        vta->guest_bytes_addr,
        vta->chase_into_ok,
        vta->archinfo_host.endness,
        vta->sigill_diag,
        vta->arch_guest,
        &vta->archinfo_guest,
        &vta->abiinfo_both,
        guest_word_type,
        vta->needs_self_check,
        vta->preamble_function,
        offB_CMSTART,
        offB_CMLEN,
        offB_GUEST_IP,
        szB_GUEST_IP,
        pap);

    vexAllocSanityCheck();

    if (irsb == NULL) {
        /* Access failure. */
        vexTEMP_clear();
        return NULL;
    }

    vassert(vta->guest_extents->n_used >= 1 && vta->guest_extents->n_used <= 3);
    vassert(vta->guest_extents->base[0] == vta->guest_bytes_addr);
    for (i = 0; i < vta->guest_extents->n_used; i++) {
        vassert(vta->guest_extents->len[i] < 10000); /* sanity */
    }

    /* bb_to_IR() could have caused pxControl to change. */
    vassert(*pxControl >= VexRegUpdSpAtMemAccess
        && *pxControl <= VexRegUpdAllregsAtEachInsn);

    /* If debugging, show the raw guest bytes for this bb. */
    if (0 || (vex_traceflags & VEX_TRACE_FE)) {
        if (vta->guest_extents->n_used > 1) {
            vex_printf("can't show code due to extents > 1\n");
        }
        else {
            /* HACK */
            const UChar* p = vta->guest_bytes;
            UInt   sum = 0;
            UInt   guest_bytes_read = (UInt)vta->guest_extents->len[0];
            vex_printf("GuestBytes %lx %u ", vta->guest_bytes_addr,
                guest_bytes_read);
            for (i = 0; i < guest_bytes_read; i++) {
                UInt b = (UInt)p[i];
                vex_printf(" %02x", b);
                sum = (sum << 1) ^ b;
            }
            vex_printf("  %08x\n\n", sum);
        }
    }

    /* Sanity check the initial IR. */
    sanityCheckIRSB(irsb, "initial IR",
        False/*can be non-flat*/, guest_word_type);

    vexAllocSanityCheck();

    /* Clean it up, hopefully a lot. */
    irsb = do_iropt_BB(irsb, specHelper, preciseMemExnsFn, *pxControl,
        vta->guest_bytes_addr,
        vta->arch_guest);

    // JRS 2016 Aug 03: Sanity checking is expensive, we already checked
    // the output of the front end, and iropt never screws up the IR by
    // itself, unless it is being hacked on.  So remove this post-iropt
    // check in "production" use.
    // sanityCheckIRSB( irsb, "after initial iropt", 
    //                  True/*must be flat*/, guest_word_type );

    if (vex_traceflags & VEX_TRACE_OPT1) {
        vex_printf("\n------------------------"
            " After pre-instr IR optimisation "
            "------------------------\n\n");
        ppIRSB(irsb);
        vex_printf("\n");
    }

    vexAllocSanityCheck();

    /* Get the thing instrumented. */
    if (vta->instrument1)
        irsb = vta->instrument1(vta->callback_opaque,
            irsb, guest_layout,
            vta->guest_extents,
            &vta->archinfo_host,
            guest_word_type, host_word_type);
    vexAllocSanityCheck();

    if (vta->instrument2)
        irsb = vta->instrument2(vta->callback_opaque,
            irsb, guest_layout,
            vta->guest_extents,
            &vta->archinfo_host,
            guest_word_type, host_word_type);

    if (vex_traceflags & VEX_TRACE_INST) {
        vex_printf("\n------------------------"
            " After instrumentation "
            "------------------------\n\n");
        ppIRSB(irsb);
        vex_printf("\n");
    }

    // JRS 2016 Aug 03: as above, this never actually fails in practice.
    // And we'll sanity check anyway after the post-instrumentation
    // cleanup pass.  So skip this check in "production" use.
    // if (vta->instrument1 || vta->instrument2)
    //    sanityCheckIRSB( irsb, "after instrumentation",
    //                     True/*must be flat*/, guest_word_type );

    /* Do a post-instrumentation cleanup pass. */
    if (vta->instrument1 || vta->instrument2) {
        do_deadcode_BB(irsb);
        irsb = cprop_BB(irsb);
        do_deadcode_BB(irsb);
        sanityCheckIRSB(irsb, "after post-instrumentation cleanup",
            True/*must be flat*/, guest_word_type);
    }

    vexAllocSanityCheck();

    if (vex_traceflags & VEX_TRACE_OPT2) {
        vex_printf("\n------------------------"
            " After post-instr IR optimisation "
            "------------------------\n\n");
        ppIRSB(irsb);
        vex_printf("\n");
    }

    return irsb;
}

