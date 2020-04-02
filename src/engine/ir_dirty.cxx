#include "engine/ir_dirty.h"
#include "engine/state_class.h"
#include "engine/z3_target_call/z3_target_call.h"

#ifdef _DEBUG
#define OUTPUT_STMTS
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
    DMEM(vctx_base & vctxb, TRsolver& s, z3::vcontext& ctx, MEM<ADDR>& mem, bool front, Bool _need_record) : MEM(vctxb, s, ctx, mem.CR3, mem.user, _need_record),
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

    void set_clear(Addr64 srs, Addr64 sa) {
        m_stack_reservve_size = srs;
        m_stack_addr = sa;
    }

    template<int MAX>
    void mount_regs(Register<MAX>* s, Addr64 grmd) {
        m_guest_regs_map_addr = grmd;
        PAGE** p = get_pointer_of_mem_page(grmd);
        p[0]->mount_regs(s);
    }

   ~DMEM()
    {
       PAGE** p = get_pointer_of_mem_page(m_guest_regs_map_addr);
       p[0]->mount_regs((TR::Register<2333>*)nullptr);
       p[0]->set_pad(0xcc);
       if(m_front){
           CR3[0] = nullptr;
       }else{
           unmap(m_stack_addr, m_stack_reservve_size);
       }
    };

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
    tval* m_irtemp = nullptr;
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
        mem.map(m_guest_regs_map_addr, 0x1000);
        mem.set_clear(m_stack_reservve_size, m_stack_addr);
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
        mem.map(m_guest_regs_map_addr, 0x1000);
        mem.set_clear(m_stack_reservve_size, m_stack_addr);
    };


    ~DState() {
        if (m_dirty_vex_mode) {
            delete ((DState*)m_dctx);
        }
    };

    inline const vex_info& info() const { return m_vex_info; }
    inline State_Tag    status() { return m_status; }
    inline void         set_status(State_Tag t) { m_status = t; };
    tval                CCall(IRCallee* cee, IRExpr** exp_args, IRType ty);
    tval                tIRExpr(IRExpr* e);
    IRSB*               translate(UChar* Host_code);
    tval                result(IRType ty) { return regs.Iex_Get(AMD64_IR_OFFSET::RAX, ty); }
    inline Addr64       getGSPTR() { return m_guest_regs_map_addr; }
    DState*             mkState(Addr64 ges) { return new DState(*this, ges); }
    void                set_ip(UChar* Haddr) { m_host_addr = Haddr; };
    inline Addr64       get_cpu_ip() { return (Addr64)m_host_addr; }

    virtual bool  StateCompression(DState const&) { return true; }
    virtual void  StateCompressMkSymbol(DState const& ) {  }; 
    inline operator z3::context& () { return m_ctx; }
    inline operator z3::vcontext& () { return m_ctx; }
    inline operator Z3_context() const { return m_ctx; }

    virtual tval      base_tIRExpr(IRExpr* e) { return m_base->tIRExpr(e).translate(m_ctx); }
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
        Addr64 stack_ret = m_stack_addr + m_stack_reservve_size - 0x8ull * MAX_GUEST_DIRTY_CALL_PARARM_NUM;
        regs.set(AMD64_IR_OFFSET::RAX, -1ll);
        regs.set(AMD64_IR_OFFSET::RSP, stack_ret);
        regs.set(AMD64_IR_OFFSET::RBP, 0x233ull);
        //code : call cee->addr
        vex_push(vex_ret_addr);
        {
            //x64 fastcall 
            const UInt assembly_args[] = { AMD64_IR_OFFSET::RCX, AMD64_IR_OFFSET::RDX, AMD64_IR_OFFSET::R8, AMD64_IR_OFFSET::R9 };
            UInt i;
            for ( i = 0; exp_args[i] != NULL; i++) {
                if (i >= (sizeof(assembly_args) / sizeof(UInt))) {
                    mem.Ist_Store(stack_ret + (ULong)(i << 3), base_tIRExpr(exp_args[i]));
                }
                else {
                    regs.set(assembly_args[i], base_tIRExpr(exp_args[i]));
                }
            };
            vassert(i <= MAX_GUEST_DIRTY_CALL_PARARM_NUM);
        };
    }

    void             init_param(IRCallee* cee, const std::initializer_list<rsval<Addr64>>& exp_args) {
        set_ip((UChar*)cee->addr);
        Addr64 stack_ret = m_stack_addr + m_stack_reservve_size - 0x8ull * MAX_GUEST_DIRTY_CALL_PARARM_NUM;
        regs.set(AMD64_IR_OFFSET::RAX, -1ll);
        regs.set(AMD64_IR_OFFSET::RSP, stack_ret);
        regs.set(AMD64_IR_OFFSET::RBP, 0x233ull);
        //code : call cee->addr
        vex_push(vex_ret_addr);
        {
            //x64 fastcall 
            const UInt assembly_args[] = { AMD64_IR_OFFSET::RCX, AMD64_IR_OFFSET::RDX, AMD64_IR_OFFSET::R8, AMD64_IR_OFFSET::R9 };
            auto v = exp_args.begin();
            UInt i;
            for (i = 0; i != exp_args.size(); i++, v++) {
                if (i >= (sizeof(assembly_args) / sizeof(UInt))) {
                    mem.Ist_Store(stack_ret + (ULong)(i << 3), *v);
                }
                else {
                    regs.set(assembly_args[i], *v);
                }
            };
            vassert(i <= MAX_GUEST_DIRTY_CALL_PARARM_NUM);
        };
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
        m_dctx->dirty_ccall(dirty->cee, dirty->args);
    }
    tval            dirty_call(IRCallee* cee, IRExpr** exp_args, IRType ty) {
        getDirtyVexCtx();
        dirty_ccall(cee, exp_args);
        return result(ty);
    }

    template<typename T>
    void vex_push(T v) {
        auto sp = regs.get<Ity_I64>(AMD64_IR_OFFSET::RSP) - 0x8ull;
        regs.set(AMD64_IR_OFFSET::RSP, sp);
        mem.store(sp, (ULong)v);
    }
    template<>
    void vex_push(const rsval<Addr64>& v) {
        auto sp = regs.get<Ity_I64>(AMD64_IR_OFFSET::RSP) - 0x8ull;
        regs.set(AMD64_IR_OFFSET::RSP, sp);
        mem.store(sp, v);
    }

    rsval<Addr64> vex_pop() {
        auto sp = regs.get<Ity_I64>(AMD64_IR_OFFSET::RSP) ;
        regs.set(AMD64_IR_OFFSET::RSP, sp + 0x8ull);
        return mem.load<Ity_I64>(sp);
    }

    inline tval ILGop(IRLoadG* lg) {
        switch (lg->cvt) {
        case ILGop_IdentV128: { return mem.load<Ity_V128>(tIRExpr(lg->addr));         }
        case ILGop_Ident64: { return mem.load<Ity_I64>(tIRExpr(lg->addr));            }
        case ILGop_Ident32: { return mem.load<Ity_I32>(tIRExpr(lg->addr));            }
        case ILGop_16Uto32: { return mem.load<Ity_I16>(tIRExpr(lg->addr)).zext<false, 16>();   }
        case ILGop_16Sto32: { return mem.load<Ity_I16>(tIRExpr(lg->addr)).sext<false, 16>();   }
        case ILGop_8Uto32: { return mem.load<Ity_I8>(tIRExpr(lg->addr)).zext<false, 8>();    }
        case ILGop_8Sto32: { return mem.load<Ity_I8>(tIRExpr(lg->addr)).sext<false, 8>();    }
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
                Addr64 stack_ret = m_stack_addr + m_stack_reservve_size - 0x8ull * MAX_GUEST_DIRTY_CALL_PARARM_NUM;
                auto rsp = regs.get<Ity_I64>(AMD64_IR_OFFSET::RSP);
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
                case Ist_Put: { regs.set(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
                case Ist_Store: { mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; };
                case Ist_WrTmp: {
                    emu[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data);
#ifdef OUTPUT_STMTS
                    std::cout << emu[s->Ist.WrTmp.tmp];
#endif
                    break; };
                case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
                    IRCAS cas = *(s->Ist.CAS.details);
                    tval addr = tIRExpr(cas.addr);//r10.value
                    tval expdLo = tIRExpr(cas.expdLo);
                    tval dataLo = tIRExpr(cas.dataLo);
                    if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
                        tval expdHi = tIRExpr(cas.expdHi);
                        tval dataHi = tIRExpr(cas.dataHi);
                        emu[cas.oldHi] = mem.Iex_Load(addr, expdLo.nbits());
                        emu[cas.oldLo] = mem.Iex_Load(addr, expdLo.nbits());
                        mem.Ist_Store(addr, dataLo);
                        mem.Ist_Store(addr + (dataLo.nbits() >> 3), dataHi);
                    }
                    else {//single
                        emu[cas.oldLo] = mem.Iex_Load(addr, expdLo.nbits());
                        mem.Ist_Store(addr, dataLo);
                    }
                    break;
                }
                case Ist_Exit: {
                    rsbool guard = tIRExpr(s->Ist.Exit.guard).tobool();
                    if (guard.real()) {
                        if ((UChar)guard & 1) {
                        Exit_guard_true:
                            vassert(s->Ist.Exit.jk == Ijk_Boring);
                            m_host_addr = (UChar*)s->Ist.Exit.dst->Ico.U64;
                            goto For_Begin;
                        };
                    }
                    else {
                        //std::vector<Vns> guard_result;
                       /* UInt eval_size = eval_all(guard_result, m_solv, guard);
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
                        }*/
                    }
                    break;
                }
                case Ist_NoOp: break;
                case Ist_IMark: {
                    if (m_status == Fork) {
                        DState* prv = newBranch;
                        newBranch = mkState(s->Ist.IMark.addr);
                        newBranch->m_solv.add_assert(!prv->m_solv.get_asserts()[0]);
                        goto EXIT;
                    };
                    m_host_addr = (UChar*)s->Ist.IMark.addr;
                    //windows dealy call ldt 
                    //00007FFAF6695BCC FF 25 F6 94 1C 00    jmp         qword ptr [00007FFAF685F0C8h]  
                    if (((UShort*)m_host_addr)[0] == 0x25FF) {
                        vassert(irsb->jumpkind == Ijk_Boring);
                        UInt offset = *(UInt*)(&m_host_addr[2]) + 6;
                        m_host_addr = ((UChar**)(&m_host_addr[offset]))[0];
                        goto For_Begin;
                    }
                    break;
                };
                case Ist_AbiHint: { m_InvokStack.push(tIRExpr(s->Ist.AbiHint.nia), regs.get<Ity_I64>(AMD64_IR_OFFSET::RBP)); break; }
                case Ist_PutI: {
                    auto ix = tIRExpr(s->Ist.PutI.details->ix);
                    vassert(ix.real());
                    regs.set(
                        s->Ist.PutI.details->descr->base + (((UInt)((s->Ist.PutI.details->bias + (int)(ix)))) % s->Ist.PutI.details->descr->nElems) * ty2length(s->Ist.PutI.details->descr->elemTy),
                        tIRExpr(s->Ist.PutI.details->data)
                    );
                    break;
                }
                case Ist_Dirty: {
                    getDirtyVexCtx();
                    IRDirty* dirty = s->Ist.Dirty.details;
                    rsbool guard = tIRExpr(dirty->guard).tobool();
                    if (guard.symb()) {
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
                    auto guard = tIRExpr(lg->guard).tobool();
                    if (guard.real()) {
                        emu[lg->dst] = (((UChar)guard & 1)) ? ILGop(lg) : tIRExpr(lg->alt);
                    }
                    else {
                        //emu[lg->dst] = ite(guard, ILGop(lg), tIRExpr(lg->alt));
                    }
                    break;
                }
                case Ist_StoreG: {
                    IRStoreG* sg = s->Ist.StoreG.details;
                    auto guard = tIRExpr(sg->guard).tobool();
                    if (guard.real()) {
                        if ((UChar)guard)
                            mem.Ist_Store(tIRExpr(sg->addr), tIRExpr(sg->data));
                    }
                    else {
                        auto addr = tIRExpr(sg->addr);
                        auto data = tIRExpr(sg->data);
                        //mem.Ist_Store(addr, ite(guard , mem.Iex_Load(addr, data.nbits()), data));
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
            case Ijk_Boring: {
                break;
            }
            case Ijk_Call:{
                m_InvokStack.push(tIRExpr(irsb->next), regs.get<Ity_I64>(AMD64_IR_OFFSET::RBP));
                break;
            }
            case Ijk_Ret: {
                m_InvokStack.pop();
                break;
            }
            default:
                goto Faild_EXIT;
            };

        Isb_next:
            auto next = tIRExpr(irsb->next).tors<false, 64>();
            if (m_status == Fork) {
                DState* prv = newBranch;
                sbool const& guard = prv->m_solv.get_asserts()[0];
                if (next.real()) {
                    newBranch = mkState(next);
                    newBranch->m_solv.add_assert(!guard);
                }
                else {
                    //std::vector<tval> result;
                    //UInt eval_size = eval_all(result, m_solv, next);
                    //if (eval_size == 0) { m_status = Death; goto EXIT; }
                    //else if (eval_size == 1) { m_host_addr = result[0].simplify(); }
                    //else {
                    //    for (auto re : result) {
                    //        Addr64 GN = re.simplify();//guest next ip
                    //        newBranch = mkState(GN);
                    //        newBranch->m_solv.add_assert(guard, False);
                    //        newBranch->m_solv.add_assert(next, re);
                    //    }
                    //}
                }
                goto EXIT;
            }

            if (next.real()) {
                m_host_addr = (UChar*)(size_t)next.tor();
            }
            else {
                //std::vector<tval> result;
                //UInt eval_size = eval_all(result, m_solv, next);
                //if (eval_size == 0) { m_status = Death; goto EXIT; }
                //else if (eval_size == 1) { m_host_addr = result[0].simplify(); }
                //else {
                //    for (auto re : result) {
                //        Addr64 GN = re.simplify();//guest next ip
                //        newBranch = mkState(GN);
                //        newBranch->m_solv.add_assert_eq(next, re);
                //    }
                //    m_status = Fork;
                //    goto EXIT;
                //}
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
            switch (error.errTag()) {
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
    VexIRDirty(State<ADDR>& state) :DState(state.info(), state.m_ctx, state.solv, state.mem), m_state(state) { 
       mem.mount_regs(&m_state.regs, m_guest_regs_map_addr);
    }
    ~VexIRDirty(){  }

    virtual tval      base_tIRExpr(IRExpr* e) override { return m_state.tIRExpr(e); }

};


class DStateIRDirty :public DState {
    DState& m_state;

    ~DStateIRDirty() {  }

    virtual tval      base_tIRExpr(IRExpr* e) override { return m_state.tIRExpr(e); }
    virtual IRSB*    translate(
        /*MOD*/ VexTranslateArgs* vta,
        /*OUT*/ VexTranslateResult* res,
        /*OUT*/ VexRegisterUpdates* pxControl,
        Pap* pap
    ) override {
        return LibVEX_FrontEnd(vta, res, pxControl, pap);
    }
public:
    DStateIRDirty(DState& state) :DState(state.m_vex_info, state.m_ctx, state.m_solv, state.mem), m_state(state) { 
        //mem.mount_regs(&m_state.regs, m_guest_regs_map_addr);
    }
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

typedef tval(*Z3_Function6)(tval&, tval&, tval&, tval&, tval&, tval&);
typedef tval(*Z3_Function5)(tval&, tval&, tval&, tval&, tval&);
typedef tval(*Z3_Function4)(tval&, tval&, tval&, tval&);
typedef tval(*Z3_Function3)(tval&, tval&, tval&);
typedef tval(*Z3_Function2)(tval&, tval&);
typedef tval(*Z3_Function1)(tval&);

#define CDFCHECK(arg0)\
if (arg0.symb()) {\
    z3_mode = True;\
    if (!cptr) { return dirty_call(cee, exp_args, ty); };\
}

tval DState::CCall(IRCallee* cee, IRExpr** exp_args, IRType ty)
{
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return tval(m_ctx, ((Function_64_0)(cee->addr))(), bitn);

    void* cptr = funcDict(cee->addr);
    if (cptr == DIRTY_CALL_MAGIC) {
        return dirty_call(cee, exp_args, ty);
    }
    tval arg0 = tIRExpr(exp_args[0]); CDFCHECK(arg0);
    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(cptr))(arg0) : tval(m_ctx, ((Function_64_1)(cee->addr))(arg0), bitn);
    tval arg1 = tIRExpr(exp_args[1]); CDFCHECK(arg1);
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(cptr))(arg0, arg1) : tval(m_ctx, ((Function_64_2)(cee->addr))(arg0, arg1), bitn);
    tval arg2 = tIRExpr(exp_args[2]); CDFCHECK(arg2);
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(cptr))(arg0, arg1, arg2) : tval(m_ctx, ((Function_64_3)(cee->addr))(arg0, arg1, arg2), bitn);
    tval arg3 = tIRExpr(exp_args[3]); CDFCHECK(arg3);
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(cptr))(arg0, arg1, arg2, arg3) : tval(m_ctx, ((Function_64_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    tval arg4 = tIRExpr(exp_args[4]); CDFCHECK(arg4);
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4) : tval(m_ctx, ((Function_64_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    tval arg5 = tIRExpr(exp_args[5]); CDFCHECK(arg5);
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5) : tval(m_ctx, ((Function_64_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
    VPANIC("not support");
}

#undef CDFCHECK


tval DState::tIRExpr(IRExpr* e)
{
    switch (e->tag) {
    case Iex_Get: { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
    case Iex_RdTmp: { return m_irtemp[e->Iex.RdTmp.tmp]; }

    //case Iex_Unop: { return Kernel::tUnop(e->Iex.Unop.op, tIRExpr(e->Iex.Unop.arg)); }
    //case Iex_Binop: { return  Kernel::tBinop(e->Iex.Binop.op, tIRExpr(e->Iex.Binop.arg1), tIRExpr(e->Iex.Binop.arg2)); }
    //case Iex_Triop: { return  Kernel::tTriop(e->Iex.Triop.details->op, tIRExpr(e->Iex.Triop.details->arg1), tIRExpr(e->Iex.Triop.details->arg2), tIRExpr(e->Iex.Triop.details->arg3)); }
    //case Iex_Qop: { return  Kernel::tQop(e->Iex.Qop.details->op, tIRExpr(e->Iex.Qop.details->arg1), tIRExpr(e->Iex.Qop.details->arg2), tIRExpr(e->Iex.Qop.details->arg3), tIRExpr(e->Iex.Qop.details->arg4)); }

    case Iex_Load: { return mem.Iex_Load(tIRExpr(e->Iex.Load.addr), e->Iex.Get.ty); }
    case Iex_Const: { return tval(m_ctx, e->Iex.Const.con); }
    case Iex_ITE: {
        rsbool cond = tIRExpr(e->Iex.ITE.cond).tobool();
        /*return (cond.real()) ?
            ((UChar)cond & 0b1) ? tIRExpr(e->Iex.ITE.iftrue) : tIRExpr(e->Iex.ITE.iffalse)
            :
            Vns(m_ctx, Z3_mk_ite(m_ctx, cond.toZ3Bool(), tIRExpr(e->Iex.ITE.iftrue), tIRExpr(e->Iex.ITE.iffalse)));*/
    }
    case Iex_CCall: { return CCall(e->Iex.CCall.cee, e->Iex.CCall.args, e->Iex.CCall.retty); }
    case Iex_GetI: {
        auto ix = tIRExpr(e->Iex.GetI.ix);   /*  [e->Iex.GetI.ix, e->Iex.GetI.bias];  */
        assert(ix.real());
        return regs.Iex_Get(e->Iex.GetI.descr->base + (((UInt)(e->Iex.GetI.bias + (int)(ix))) % e->Iex.GetI.descr->nElems) * ty2length(e->Iex.GetI.descr->elemTy), e->Iex.GetI.descr->elemTy);
    };
    case Iex_GSPTR: {
        return tval(m_ctx, (size_t)getGSPTR());
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
    sbool m_condition;
    static bool StateCompression(DState& a, DState const& next) {
        bool ret = a.m_InvokStack == next.m_InvokStack;// 压缩条件
        return ret && a.StateCompression(next);//支持扩展条件
    }

    static void StateCompressMkSymbol(DState& a, DState const& newState) {
        a.m_InvokStack = newState.m_InvokStack;// 使其满足压缩条件
        a.StateCompressMkSymbol(newState);//支持
    }

    std::vector<sbool> const& get_asserts() const { return m_state.m_solv.get_asserts(); };

public:
    DStateCmprsInterface(
        cmpr::CmprsContext<DState, State_Tag>& ctx,
        DState& self,
        cmpr::StateType type
    ) :
        m_ctx(ctx), m_state(self), m_type(type), m_condition(cmpr::logic_and(get_asserts()).translate(m_ctx.ctx()))
    { };

    cmpr::CmprsContext<DState, State_Tag>& cctx() { return m_ctx; }
    cmpr::StateType type() { return m_type; };

    sbool const& get_assert() {
        return m_condition;
    }

    void get_write_map(std::hash_map<Addr64, bool>& record) {
        if (m_state.regs.getRecord()) {
            for (auto offset : *m_state.regs.getRecord()) {
                record[offset];
            }
        }
        for (auto mcm : m_state.mem.change_map()) {
            vassert(mcm.second->getRecord() != NULL);
            for (auto offset : *(mcm.second->getRecord())) {
                auto Address = mcm.first + offset;
                auto p = m_state.mem.get_mem_page(Address);
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

    PACK mem_Load(Addr64 addr) {
        return m_state.mem.load<Ity_I64>(addr).translate(m_ctx.ctx());
    }

    PACK reg_Get(UInt offset) {
        return m_state.regs.get<Ity_I64>(offset).translate(m_ctx.ctx());
    }

    PACK read(Addr64 addr) {
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
            sbool condition = state.conditions().translate(*nbranch);
#ifdef  PPCMPR
            printf("%s\n", Z3_ast_to_string(condition, condition));
#endif //  _DEBUG
            nbranch->m_solv.add_assert(condition);
            std::hash_map<Addr64, cmpr::GPMana> const& cm = state.changes();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator itor = cm.begin();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator end = cm.end();

            for (; itor != end; itor++) {
                Addr64 addr = itor->first;
                auto value = itor->second.get().translate(*nbranch);
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
                    nbranch->regs.set(addr, value);
                }
            }
        }
    }
    else {
        for (cmpr::Compress<DStateCmprsInterface, DState, State_Tag>::Iterator::StateRes state : cmp) {
            sbool condition = state.conditions();
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
                auto value = itor->second.get();
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
                    regs.set(addr, value);
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
void dirty_call_np(DirtyCtx dctx, const HChar* name, void* func, const std::initializer_list<rsval<Addr64>>& parms) {
    VexIRDirty<ADDR>* d = (VexIRDirty<ADDR>*)dctx;
    IRCallee cee = { (Int)parms.size() , name, func, 0xffffffff };
    vexSetAllocModeTEMP_and_save_curr();
    d->init_param(&cee, parms);
    d->start();
}

template<typename ADDR>
void dirty_run(DirtyCtx dctx, IRDirty* dirty) {
    VexIRDirty<ADDR>* d = (VexIRDirty<ADDR>*)dctx;
    dirty_ccall<ADDR>(dctx, dirty->cee, dirty->args);
}

template<typename ADDR>
tval dirty_result(DirtyCtx dctx, IRType rty) {
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
template void dirty_call_np<Addr32>(DirtyCtx dctx, const HChar* name, void* func, const std::initializer_list<rsval<Addr64>>& parms);
template void dirty_call_np<Addr64>(DirtyCtx dctx, const HChar* name, void* func, const std::initializer_list<rsval<Addr64>>& parms);
template tval dirty_result<Addr32>(DirtyCtx dctx, IRType rty);
template tval dirty_result<Addr64>(DirtyCtx dctx, IRType rty);



