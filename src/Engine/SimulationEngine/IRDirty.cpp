
#include "IRDirty.hpp"

extern "C" {
#include "libvex_guest_x86.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_arm.h"
#include "libvex_guest_arm64.h"
#include "libvex_guest_mips32.h"
#include "libvex_guest_mips64.h"
#include "libvex_guest_ppc32.h"
#include "libvex_guest_ppc64.h"
#include "libvex_guest_s390x.h"
}

class Register_Dirty :public Register<REGISTER_LEN> {
    IRDirty* m_d;
public:
    inline Register_Dirty(TRcontext& ctx, Bool _need_record) :Register(ctx, _need_record) {

    }

    inline Register_Dirty(Register<REGISTER_LEN>& father_regs, TRcontext& ctx, Bool _need_record) : Register(father_regs, ctx, _need_record) {

    }
    void setIRDirty(IRDirty* d) { m_d = d; }
};




static inline bool check_access_guest_regs(IRDirty* d) {
    Int i;
    for (i = 0; i < d->nFxState; i++) {
        vex_printf(" ");
        ppIREffect(d->fxState[i].fx);
        vex_printf("-gst(%u,%u", (UInt)d->fxState[i].offset,
            (UInt)d->fxState[i].size);
        if (d->fxState[i].nRepeats > 0) {
            vex_printf(",reps%u,step%u", (UInt)d->fxState[i].nRepeats,
                (UInt)d->fxState[i].repeatLen);
        }
        vex_printf(")");
    }
}

static inline bool check_access_guest_mem(IRDirty* d) {
    if (d->mFx != Ifx_None) {
        vex_printf(" ");
        ppIREffect(d->mFx);
        vex_printf("-mem(");
        ppIRExpr(d->mAddr);
        vex_printf(",%d)", d->mSize);
    }
}

template<typename ADDR>
class Dirty_Mem: public MEM<Addr64> {
    State<ADDR>& m_state;
    Addr64 m_guest_regs_map_addr = 0;
public:
    Dirty_Mem(State<ADDR> &state) :MEM<Addr64>(dirty_cp_mem{}, state.mem), m_state(state)
    {
        vassert(REGISTER_LEN < 0x1000);
        CR3 = state.mem.CR3;
        user = state.mem.user;
    };

    void init(Addr64 guest_regs_map_addr, IRDirty* d) {
        m_guest_regs_map_addr = guest_regs_map_addr;
        for (Int i = 0; i < d->nFxState; i++) {
            switch (d->fxState[i].fx) {
            case Ifx_None: continue;
            case Ifx_Modify:
            case Ifx_Read: { 
                Ist_Store(m_guest_regs_map_addr + (UInt)d->fxState[i].offset, m_state.regs.Iex_Get(d->fxState[i].offset, d->fxState[i].size));
                if (d->fxState[i].nRepeats > 0) {
                    for (UInt repeat = 0; repeat < d->fxState[i].nRepeats; repeat++) {
                        Ist_Store(m_guest_regs_map_addr + (UInt)d->fxState[i].offset + (UInt)d->fxState[i].repeatLen * repeat, m_state.regs.Iex_Get(d->fxState[i].offset, d->fxState[i].size));
                    }
                }
                break; 
            }
            case Ifx_Write: break;
            default: vpanic("ppIREffect");
            }
        }
    }

    void set_Ifx_Modify(IRDirty* d) {
        for (Int i = 0; i < d->nFxState; i++) {
            switch (d->fxState[i].fx) {
            case Ifx_None: continue;
            case Ifx_Modify:
            case Ifx_Write:{
                m_state.regs.Ist_Put(d->fxState[i].offset, Iex_Load(m_guest_regs_map_addr + (UInt)d->fxState[i].offset, (IRType)(d->fxState[i].size << 3)));
                if (d->fxState[i].nRepeats > 0) {
                    for (UInt repeat = 0; repeat < d->fxState[i].nRepeats; repeat++) {
                        m_state.regs.Ist_Put(d->fxState[i].offset, Iex_Load(m_guest_regs_map_addr + (UInt)d->fxState[i].offset + (UInt)d->fxState[i].repeatLen * repeat, (IRType)(d->fxState[i].size << 3)));
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


class TRsolver;
template<typename ADDR>
class VexIRDirty :public Vex_Info {
    Pap m_pap;
    bool m_front;
    TRcontext& m_ctx;
    TRsolver& solv;
    Register<REGISTER_LEN>  regs;

    Dirty_Mem<ADDR> mem;
    Addr64 m_stack_reservve_size = 0x1000;
    Addr64 m_stack_addr;
    Addr64 m_guest_regs_map_addr;


    Addr64 m_org_guest_addr;
    State<ADDR>& m_state;
    const Addr64 vex_ret_addr = 0x1ull;

    VexTranslateArgs m_vta_chunk;
    VexGuestExtents m_vge_chunk;
public:
    VexIRDirty(State<ADDR>& state, bool is_front) :
        m_ctx(state),
        m_state(state),
        solv(state.solv),
        regs(m_ctx, true),
        mem(state),
        m_org_guest_addr(state.get_cpu_ip()),
        m_front(is_front),
        m_stack_addr(mem.find_block_reverse(((ADDR)0) - 0x10000, m_stack_reservve_size)),
        m_guest_regs_map_addr(mem.find_block_forward(0x1000, REGISTER_LEN))
    {
        m_pap.state = &m_state;
        m_pap.n_page_mem = _n_page_mem;
        m_pap.guest_max_insns = 100;
        mem.map(m_stack_addr, m_stack_reservve_size);
        mem.map(m_guest_regs_map_addr, 1000);
        init_vta_chunk(m_vta_chunk, m_vge_chunk, VexArchAMD64, 0);
    };
    Vns tIRExpr(IRExpr* e);
    IRSB* translate(UChar* Host_code);
    void dirty_call(Vns *ret, IRType ty, IRDirty* dirty) {
        auto guard = m_state.tIRExpr(dirty->guard);
        if (guard.symbolic()) {
            throw ForkException("auto guard = m_state.tIRExpr(dirty->guard); symbolic");
        }
        if (((UChar)guard) & 1) {
            mem.init(m_guest_regs_map_addr, dirty);
            if (dirty->tmp != IRTemp_INVALID) {
                *ret = t_CCall(dirty->cee, dirty->args, ty);
            }
            else {
                t_CCall(dirty->cee, dirty->args, Ity_I64);
            }
            mem.set_Ifx_Modify(dirty);
        }
    }

    inline Addr64 getGSPTR() { return m_guest_regs_map_addr; }
    Vns t_CCall(IRCallee* cee, IRExpr** exp_args, IRType rety);
private:
    Vns ILGop(IRLoadG* lg);
    Vns CCall(IRCallee* cee, IRExpr** exp_args, IRType ty);
    
    template<typename T>
    void vex_push(T v) {
        Vns sp = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rsp) - 0x8ull;
        regs.Ist_Put(AMD64_IR_OFFSET::rsp, sp);
        mem.Ist_Store(sp, (ULong)v);
    }
    template<>
    void vex_push(Vns const& v) {
        Vns sp = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rsp) - 0x8ull;
        regs.Ist_Put(AMD64_IR_OFFSET::rsp, sp);
        mem.Ist_Store(sp, v);
    }

    Vns vex_pop() {
        Vns sp = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rsp) + 0x8ull;
        regs.Ist_Put(AMD64_IR_OFFSET::rsp, sp);
        return mem.Iex_Load<Ity_I64>(sp, sp);
    }

};




template<typename ADDR>
IRSB* VexIRDirty<ADDR>::translate(UChar* Host_code) {
    m_pap.start_swap = 2;
    m_vta_chunk.guest_bytes = Host_code;
    m_vta_chunk.guest_bytes_addr = (Addr64)(Host_code);
    VexRegisterUpdates pxControl;
    VexTranslateResult res;
    return LibVEX_FrontEnd(&m_vta_chunk, &res, &pxControl, &m_pap);
}



template<typename ADDR>
inline Vns VexIRDirty<ADDR>::ILGop(IRLoadG* lg) {
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

template<typename ADDR>
Vns VexIRDirty<ADDR>::CCall(IRCallee* cee, IRExpr** exp_args, IRType ty)
{
   /* Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return Vns(m_ctx, ((Function_0)(cee->addr))(), bitn);
    Vns arg0 = tIRExpr(exp_args[0]);
    if (arg0.symbolic()) z3_mode = True;
    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(funcDict(cee->addr)))(arg0) : symbolic_check(m_ctx, ((Function_1)(cee->addr))(arg0), bitn);
    Vns arg1 = tIRExpr(exp_args[1]);
    if (arg1.symbolic()) z3_mode = True;
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(funcDict(cee->addr)))(arg0, arg1) : symbolic_check(m_ctx, ((Function_2)(cee->addr))(arg0, arg1), bitn);
    Vns arg2 = tIRExpr(exp_args[2]);
    if (arg2.symbolic()) z3_mode = True;
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(funcDict(cee->addr)))(arg0, arg1, arg2) : symbolic_check(m_ctx, ((Function_3)(cee->addr))(arg0, arg1, arg2), bitn);
    Vns arg3 = tIRExpr(exp_args[3]);
    if (arg3.symbolic()) z3_mode = True;
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(funcDict(cee->addr)))(arg0, arg1, arg2, arg3) : symbolic_check(m_ctx, ((Function_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    Vns arg4 = tIRExpr(exp_args[4]);
    if (arg4.symbolic()) z3_mode = True;
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(funcDict(cee->addr)))(arg0, arg1, arg2, arg3, arg4) : symbolic_check(m_ctx, ((Function_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    Vns arg5 = tIRExpr(exp_args[5]);
    if (arg5.symbolic()) z3_mode = True;
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(funcDict(cee->addr)))(arg0, arg1, arg2, arg3, arg4, arg5) : symbolic_check(m_ctx, ((Function_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);*/

}

template<typename ADDR>
inline Vns VexIRDirty<ADDR>::tIRExpr(IRExpr* e)
{
    switch (e->tag) {
    case Iex_Get: { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
    case Iex_RdTmp: { return ir_temp[e->Iex.RdTmp.tmp]; }
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


template<typename ADDR>
Vns VexIRDirty<ADDR>::t_CCall(IRCallee* cee, IRExpr** exp_args, IRType ty) {
    Addr64 stack_ret = m_stack_addr + m_stack_reservve_size - 0x8ull*6;
    regs.Ist_Put(AMD64_IR_OFFSET::rsp, stack_ret);
    regs.Ist_Put(AMD64_IR_OFFSET::rbp, 0x233ull);
    {
        //const UInt assembly_args[] = { AMD64_IR_OFFSET::rdi, AMD64_IR_OFFSET::rsi, AMD64_IR_OFFSET::rdx, AMD64_IR_OFFSET::rcx, AMD64_IR_OFFSET::r8, AMD64_IR_OFFSET::r9 };
        const UInt assembly_args[] = { AMD64_IR_OFFSET::rcx, AMD64_IR_OFFSET::rdx, AMD64_IR_OFFSET::r8, AMD64_IR_OFFSET::r9 };
        for (UInt i = 0; exp_args[i] != NULL; i++) {
            if (i >= (sizeof(assembly_args) / sizeof(UInt))) {
                vex_push(tIRExpr(exp_args[i]));
            }
            else {
                regs.Ist_Put(assembly_args[i], tIRExpr(exp_args[i]));
            }
        };
    };
    vex_push(vex_ret_addr);
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    UChar* host_addr = (UChar*)cee->addr;
    while(true) {
        if (reinterpret_cast<Addr64>(host_addr) == vex_ret_addr) {
            Vns rsp = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rsp);
            if (rsp.real()) {
                vassert((ULong)rsp == stack_ret);
                break;
            }
            VPANIC("????");
        }
    For_Begin:
        IRSB* irsb = translate(host_addr);
        IRStmt* s = irsb->stmts[0];
        for (UInt stmtn = 0; stmtn < irsb->stmts_used;
            s = irsb->stmts[++stmtn])
        {
            ppIRStmt(s);
            switch (s->tag) {
            case Ist_Put: { regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
            case Ist_Store: { mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; };
            case Ist_WrTmp: {
                ir_temp[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data);
                std::cout << ir_temp[s->Ist.WrTmp.tmp];
                break; };
            case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
                IRCAS cas = *(s->Ist.CAS.details);
                Vns addr = tIRExpr(cas.addr);//r10.value
                Vns expdLo = tIRExpr(cas.expdLo);
                Vns dataLo = tIRExpr(cas.dataLo);
                if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
                    Vns expdHi = tIRExpr(cas.expdHi);
                    Vns dataHi = tIRExpr(cas.dataHi);
                    ir_temp[cas.oldHi] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                    ir_temp[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                    mem.Ist_Store(addr, dataLo);
                    mem.Ist_Store(addr + (dataLo.bitn >> 3), dataHi);
                }
                else {//single
                    ir_temp[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
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
                        host_addr = (UChar*)s->Ist.Exit.dst->Ico.U64;
                        if (s->Ist.Exit.jk <= Ijk_Ret)
                        {
                            goto For_Begin;
                        }
                    }
                }
                else {
                    UInt eval_size = eval_all(guard_result, solv, guard);
                    vassert(eval_size <= 2);
                    if (eval_size == 0) { /*status = Death; goto EXIT;*/ }
                    if (eval_size == 1) {
                        if (((UChar)guard_result[0].simplify()) & 1)
                            goto Exit_guard_true;
                    }
                    if (eval_size == 2) {
                        if (s->Ist.Exit.jk > Ijk_Ret) {
                            solv.add_assert(guard, False);
                        }
                        else {
                            /*branchChunks.emplace_back(BranchChunk(s->Ist.Exit.dst->Ico.U64, Vns(m_ctx, 0), guard, True));
                            status = Fork;*/
                        }
                    }
                }
                break;
            }
            case Ist_NoOp: break;
            case Ist_IMark: { 
                host_addr = (UChar*)s->Ist.IMark.addr;
                break;
            };
            case Ist_AbiHint: { break; }
            case Ist_PutI: {
                auto ix = tIRExpr(s->Ist.PutI.details->ix);
                if (ix.real()) {
                    regs.Ist_Put(
                        s->Ist.PutI.details->descr->base + (((UInt)((s->Ist.PutI.details->bias + (int)(ix)))) % s->Ist.PutI.details->descr->nElems) * ty2length(s->Ist.PutI.details->descr->elemTy),
                        tIRExpr(s->Ist.PutI.details->data)
                    );
                }
                else {
                    vassert(0);
                }
                break;
            }
            case Ist_Dirty: {
                VPANIC("no");
                break;
            }
            case Ist_LoadG: {
                IRLoadG* lg = s->Ist.LoadG.details;
                auto guard = tIRExpr(lg->guard);
                if (guard.real()) {
                    ir_temp[lg->dst] = (((UChar)guard&1)) ? ILGop(lg) : tIRExpr(lg->alt);
                }
                else {
                    ir_temp[lg->dst] = ite(guard == 1, ILGop(lg), tIRExpr(lg->alt));
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
                vex_printf("addr: %p what ppIRStmt %d\n", host_addr, s->tag);
                VPANIC("what ppIRStmt");
            }
            }
            vex_printf("\n");
        }

        switch (irsb->jumpkind) {
        case Ijk_Boring:        break;
        case Ijk_Call:          break;
        case Ijk_Ret:           break;
        default: //Ijk_SigTRAP


        };

    Isb_next:
        Vns next = tIRExpr(irsb->next).simplify();
        if (next.real()) {
            host_addr = next;
        }
        else {
            VPANIC("GG");
        }

    }
    return regs.Iex_Get(AMD64_IR_OFFSET::rax, ty);
}

template<typename ADDR>
DirtyCtx dirty_context(State<ADDR>* s) {
    return (DirtyCtx)new VexIRDirty<ADDR>(*s, true);
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
void dirty_run(DirtyCtx dctx, Vns* ret, IRType ty, IRDirty* dirty) {
    ((VexIRDirty<ADDR>*)dctx)->dirty_call(ret, ty, dirty);
}
template<typename ADDR>
Vns dirty_ccall(DirtyCtx dctx, IRType ty, IRCallee* cee, IRExpr** args) {
    return ((VexIRDirty<ADDR>*)dctx)->t_CCall(cee, args, ty);
}

template DirtyCtx dirty_context(State<Addr32>* s);
template DirtyCtx dirty_context(State<Addr64>* s);
template Addr64 dirty_get_gsptr<Addr32>(DirtyCtx dctx);
template Addr64 dirty_get_gsptr<Addr64>(DirtyCtx dctx);
template void dirty_run<Addr32>(DirtyCtx dctx, Vns* ret, IRType ty, IRDirty* dirty);
template void dirty_run<Addr64>(DirtyCtx dctx, Vns* ret, IRType ty, IRDirty* dirty);
template void dirty_context_del<Addr32>(DirtyCtx dctx);
template void dirty_context_del<Addr64>(DirtyCtx dctx);
template Vns dirty_ccall<Addr32>(DirtyCtx dctx, IRType ty, IRCallee* cee, IRExpr** args);
template Vns dirty_ccall<Addr64>(DirtyCtx dctx, IRType ty, IRCallee* cee, IRExpr** args);