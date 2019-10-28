/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    TriggerBug.cpp: 
Abstract:
    API list;
Author:
    WXC 2019-05-31.
Revision History:
--*/


//#undef _DEBUG
#define DLL_EXPORTS
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\TriggerBug-asong.xml"
#define INIFILENAME "C:/Users/bibi/Desktop/TriggerBug/PythonFrontEnd/TriggerBug-default32.xml"
#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\fight\\fight.xml"
#define INIFILENAME "C:\\Users\\bibi\\Desktop\\reverse\\kanXue\\CTF Commit\\ckm.xml"
#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\Roads\\Roads.xml"


#include "engine.hpp"
#define vpanic(...) printf("%s line %d",__FILE__,__LINE__); vpanic(__VA_ARGS__);

#include "SimulationEngine/State_class.hpp"
#include "Z3_Target_Call/Guest_Helper.hpp"




UInt flag_count = 0;
UInt flag_max_count = 0;

class DebugState : public State {
public:
    DebugState(const char* filename, Addr64 gse, Bool _need_record) :
        State(filename, gse, _need_record)
    { };

    DebugState(DebugState* father_state, Addr64 gse) :
        State(father_state, gse)
    { };


    void spIRExpr(const IRExpr* e)
    {
        Int i;
        switch (e->tag) {
        case Iex_Binder:
            vex_printf("BIND-%d", e->Iex.Binder.binder);
            break;
        case Iex_Get:
            vex_printf("GET:");
            ppIRType(e->Iex.Get.ty);
            vex_printf("(%d)", e->Iex.Get.offset);
            break;
        case Iex_GetI:
            vex_printf("GETI");
            ppIRRegArray(e->Iex.GetI.descr);
            vex_printf("[");
            spIRExpr(e->Iex.GetI.ix);
            vex_printf(",%d]", e->Iex.GetI.bias);
            break;
        case Iex_RdTmp:
            spIRTemp(e->Iex.RdTmp.tmp);
            break;
        case Iex_Qop: {
            const IRQop* qop = e->Iex.Qop.details;
            ppIROp(qop->op);
            vex_printf("(");
            spIRExpr(qop->arg1);
            vex_printf(",");
            spIRExpr(qop->arg2);
            vex_printf(",");
            spIRExpr(qop->arg3);
            vex_printf(",");
            spIRExpr(qop->arg4);
            vex_printf(")");
            break;
        }
        case Iex_Triop: {
            const IRTriop* triop = e->Iex.Triop.details;
            ppIROp(triop->op);
            vex_printf("(");
            spIRExpr(triop->arg1);
            vex_printf(",");
            spIRExpr(triop->arg2);
            vex_printf(",");
            spIRExpr(triop->arg3);
            vex_printf(")");
            break;
        }
        case Iex_Binop:
            ppIROp(e->Iex.Binop.op);
            vex_printf("(");
            spIRExpr(e->Iex.Binop.arg1);
            vex_printf(",");
            spIRExpr(e->Iex.Binop.arg2);
            vex_printf(")");
            break;
        case Iex_Unop:
            ppIROp(e->Iex.Unop.op);
            vex_printf("(");
            spIRExpr(e->Iex.Unop.arg);
            vex_printf(")");
            break;
        case Iex_Load:
            vex_printf("LD%s:", e->Iex.Load.end == Iend_LE ? "le" : "be");
            ppIRType(e->Iex.Load.ty);
            vex_printf("(");
            spIRExpr(e->Iex.Load.addr);
            vex_printf(")");
            break;
        case Iex_Const:
            ppIRConst(e->Iex.Const.con);
            break;
        case Iex_CCall:
            ppIRCallee(e->Iex.CCall.cee);
            vex_printf("(");
            for (i = 0; e->Iex.CCall.args[i] != NULL; i++) {
                IRExpr* arg = e->Iex.CCall.args[i];
                spIRExpr(arg);

                if (e->Iex.CCall.args[i + 1] != NULL) {
                    vex_printf(",");
                }
            }
            vex_printf("):");
            ppIRType(e->Iex.CCall.retty);
            break;
        case Iex_ITE:
            vex_printf("ITE(");
            spIRExpr(e->Iex.ITE.cond);
            vex_printf(",");
            spIRExpr(e->Iex.ITE.iftrue);
            vex_printf(",");
            spIRExpr(e->Iex.ITE.iffalse);
            vex_printf(")");
            break;
        case Iex_VECRET:
            vex_printf("VECRET");
            break;
        case Iex_GSPTR:
            vex_printf("GSPTR");
            break;
        default:
            vpanic("ppIRExpr");
        }
    }

    void spIRTemp(IRTemp tmp)
    {
        if (tmp == IRTemp_INVALID)
            vex_printf("IRTemp_INVALID");
        else
        {
            vex_printf("t%u: ", tmp);
            std::cout << ir_temp[t_index][tmp];
        }
    }

    void spIRPutI(const IRPutI* puti)
    {
        vex_printf("PUTI");
        ppIRRegArray(puti->descr);
        vex_printf("[");
        ppIRExpr(puti->ix);
        vex_printf(",%d] = ", puti->bias);
        ppIRExpr(puti->data);
    }


    void spIRStmt(const IRStmt* s)
    {
        if (!s) {
            vex_printf("!!! IRStmt* which is NULL !!!");
            return;
        }
        switch (s->tag) {
        case Ist_NoOp:
            vex_printf("IR-NoOp");
            break;
        case Ist_IMark:
            vex_printf("------ IMark(0x%llx, %u, %u) ------",
                s->Ist.IMark.addr, s->Ist.IMark.len,
                (UInt)s->Ist.IMark.delta);
            break;
        case Ist_AbiHint:
            vex_printf("====== AbiHint(");
            spIRExpr(s->Ist.AbiHint.base);
            vex_printf(", %d, ", s->Ist.AbiHint.len);
            spIRExpr(s->Ist.AbiHint.nia);
            vex_printf(") ======");
            break;
        case Ist_Put:
            vex_printf("PUT(%d) = ", s->Ist.Put.offset);
            spIRExpr(s->Ist.Put.data);
            break;
        case Ist_PutI:
            ppIRPutI(s->Ist.PutI.details);
            break;
        case Ist_WrTmp:
            ppIRTemp(s->Ist.WrTmp.tmp);
            vex_printf(" = ");
            spIRExpr(s->Ist.WrTmp.data);
            break;
        case Ist_Store:
            vex_printf("ST%s(", s->Ist.Store.end == Iend_LE ? "le" : "be");
            spIRExpr(s->Ist.Store.addr);
            vex_printf(") = ");
            spIRExpr(s->Ist.Store.data);
            break;
        case Ist_StoreG:
            ppIRStoreG(s->Ist.StoreG.details);
            break;
        case Ist_LoadG:
            ppIRLoadG(s->Ist.LoadG.details);
            break;
        case Ist_CAS:
            ppIRCAS(s->Ist.CAS.details);
            break;
        case Ist_LLSC:
            if (s->Ist.LLSC.storedata == NULL) {
                spIRTemp(s->Ist.LLSC.result);
                vex_printf(" = LD%s-Linked(",
                    s->Ist.LLSC.end == Iend_LE ? "le" : "be");
                spIRExpr(s->Ist.LLSC.addr);
                vex_printf(")");
            }
            else {
                spIRTemp(s->Ist.LLSC.result);
                vex_printf(" = ( ST%s-Cond(",
                    s->Ist.LLSC.end == Iend_LE ? "le" : "be");
                spIRExpr(s->Ist.LLSC.addr);
                vex_printf(") = ");
                spIRExpr(s->Ist.LLSC.storedata);
                vex_printf(" )");
            }
            break;
        case Ist_Dirty:
            ppIRDirty(s->Ist.Dirty.details);
            break;
        case Ist_MBE:
            vex_printf("IR-");
            ppIRMBusEvent(s->Ist.MBE.event);
            break;
        case Ist_Exit:
            vex_printf("if (");
            spIRExpr(s->Ist.Exit.guard);
            vex_printf(") { PUT(%d) = ", s->Ist.Exit.offsIP);
            ppIRConst(s->Ist.Exit.dst);
            vex_printf("; exit-");
            ppIRJumpKind(s->Ist.Exit.jk);
            vex_printf(" } ");
            break;
        default:
            vpanic("ppIRStmt");
        }
    }



    void start(Bool first_bkp_pass) {
        //auto TIB = (NT_TIB64*)__readgsqword(offsetof(NT_TIB64, Self));

        if (this->status != NewState) {
            vex_printf("this->status != NewState");
            return;
        }
        Bool NEED_CHECK = ppStmts;
        Bool is_first_bkp_pass = False;
        Addr64 hook_bkp = NULL;
        status = Running;
        thread_register();
        t_index = temp_index();
        Vns* irTemp = ir_temp[t_index];
        this->is_dynamic_block = false;

        Bool t_NEED_CHECK = NEED_CHECK;
        Bool t_traceJmp = traceJmp;
        ADDR t_guest_start = 0;
        Bool t_TraceSymbolic = TraceSymbolic;


    Begin_try:

        try {
            try {
                if (first_bkp_pass)
                    if ((UChar)mem.Iex_Load<Ity_I8>(guest_start) == 0xCC) {
                        is_first_bkp_pass = True;
                        goto bkp_pass;
                    }
                for (;;) {
                For_Begin:
                    IRSB* irsb = BB2IR();
                    guest_start_of_block = guest_start;
                    //ppIRSB(irsb);
                    if (traceJmp)
                        vex_printf("Jmp: %llx \n", guest_start);

                    if (guest_start == t_guest_start) {
                        t_NEED_CHECK = (NEED_CHECK) ? NEED_CHECK : t_NEED_CHECK;
                        t_traceJmp = traceJmp ? traceJmp : t_traceJmp;
                        NEED_CHECK = False;
                        traceJmp = False;
                    }
                    else {
                        t_guest_start = guest_start;
                        NEED_CHECK = t_NEED_CHECK;
                        traceJmp = t_traceJmp;
                    }
                For_Begin_NO_Trans:
                    for (UInt stmtn = 0; stmtn < irsb->stmts_used; stmtn++) {
                        IRStmt* s = irsb->stmts[stmtn];
                        if (guest_start == traceIrAddrress) {
                            NEED_CHECK = True;
                            t_NEED_CHECK = True;
                        }
                        if (NEED_CHECK) ppIRStmt(s);
                        switch (s->tag) {
                        /*case Ist_Put: { regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
                        case Ist_Store: { mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; };
                        case Ist_WrTmp: { irTemp[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data);
                            if (NEED_CHECK)std::cout << irTemp[s->Ist.WrTmp.tmp] << std::endl;
                            break;
                        }*/

                        case Ist_Put: {
                            Vns regData = tIRExpr(s->Ist.Put.data);
                            regs.Ist_Put(s->Ist.Put.offset, regData);
                            if (TraceSymbolic) {
                                Vns data = regData.simplify();
                                if (data.symbolic()) {
                                    vex_printf("ADDR: %p\t", guest_start);
                                    spIRStmt(s);
                                    std::cout << irTemp[s->Ist.WrTmp.tmp] << std::endl;
                                    vex_printf("\n");
                                }
                            }

                            break; }
                        case Ist_Store: {
                            Vns addr = tIRExpr(s->Ist.Store.addr);
                            Vns mData = tIRExpr(s->Ist.Store.data);
                            mem.Ist_Store(addr, mData);
                            if (TraceSymbolic) {
                                Vns saddr = addr.simplify();
                                Vns smData = mData.simplify();
                                if (saddr.symbolic() || smData.symbolic()) {
                                    vex_printf("ADDR: %p\t", guest_start);
                                    spIRStmt(s);
                                    vex_printf("\n");
                                }
                            }
                            break;
                        };
                        case Ist_WrTmp: {irTemp[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data);
                            if (NEED_CHECK)std::cout << irTemp[s->Ist.WrTmp.tmp] << std::endl;

                            if (TraceSymbolic) {
                                Vns data = irTemp[s->Ist.WrTmp.tmp].simplify();
                                if (data.symbolic()) {
                                    vex_printf("ADDR: %p\t", guest_start);
                                    spIRStmt(s);
                                    std::cout << irTemp[s->Ist.WrTmp.tmp] << std::endl;
                                    vex_printf("\n");
                                }
                            }

                            break;
                        }

                        case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
                            bool xchgbv = false;
                            while (!xchgbv) {
                                __asm__ __volatile("xchgb %b0,%1":"=r"(xchgbv) : "m"(unit_lock), "0"(xchgbv) : "memory");
                            }
                            IRCAS cas = *(s->Ist.CAS.details);
                            Vns addr = tIRExpr(cas.addr);//r10.value
                            Vns expdLo = tIRExpr(cas.expdLo);
                            Vns dataLo = tIRExpr(cas.dataLo);
                            if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
                                Vns expdHi = tIRExpr(cas.expdHi);
                                Vns dataHi = tIRExpr(cas.dataHi);
                                irTemp[cas.oldHi] = mem.Iex_Load(addr, length2ty(expdLo.bitn));
                                irTemp[cas.oldLo] = mem.Iex_Load(addr, length2ty(expdLo.bitn));
                                mem.Ist_Store(addr, dataLo);
                                mem.Ist_Store(addr + (dataLo.bitn >> 3), dataHi);
                            }
                            else {//single
                                irTemp[cas.oldLo] = mem.Iex_Load(addr, length2ty(expdLo.bitn));
                                mem.Ist_Store(addr, dataLo);
                            }
                            unit_lock = true;
                            break;
                        }
                        case Ist_Exit: {
                            Vns guard = tIRExpr(s->Ist.Exit.guard);
                            if (guard.real()) {
                                if ((UChar)guard) {
                                Exit_guard_true:
                                    if (s->Ist.Exit.jk != Ijk_Boring
                                        && s->Ist.Exit.jk != Ijk_Call
                                        && s->Ist.Exit.jk != Ijk_Ret
                                        )
                                    {
                                        status = Ijk_call(s->Ist.Exit.jk);
                                        if (status != Running) {
                                            goto EXIT;
                                        }
                                        if (delta) {
                                            guest_start = guest_start + delta;
                                            delta = 0;
                                            goto For_Begin;
                                        }
                                    }
                                    else {
                                        guest_start = s->Ist.Exit.dst->Ico.U64;
                                        hook_bkp = NULL;
                                        goto For_Begin;
                                    }
                                }
                                break;
                            }
                            else {
                                int rgurd[2];
                                std::vector<Z3_ast> guard_result;
                                int num_guard = eval_all(guard_result, solv, guard);
                                if (num_guard == 1) {
                                    Z3_get_numeral_int(m_ctx, guard_result[0], &rgurd[0]);
                                    Z3_dec_ref(m_ctx, guard_result[0]);
                                    if (rgurd[0]) {
                                        add_assert(guard, True);
                                        goto Exit_guard_true;
                                    }
                                    else {
                                        add_assert(guard, False);
                                    }
                                }
                                else if (num_guard == 2) {
                                    Z3_dec_ref(m_ctx, guard_result[0]);
                                    Z3_dec_ref(m_ctx, guard_result[1]);
                                    struct _bs {
                                        ADDR addr;
                                        Z3_ast _s_addr;
                                        bool _not;
                                    };
                                    std::vector<_bs> bs_v;
                                    bs_v.emplace_back(_bs{ s->Ist.Exit.dst->Ico.U64 ,NULL, True });
                                    Vns _next = tIRExpr(irsb->next);
                                    if (_next.real()) {
                                        bs_v.emplace_back(_bs{ _next ,_next, False });
                                    }
                                    else {
                                        std::vector<Z3_ast> next_result;
                                        eval_all(next_result, solv, _next);
                                        for (auto&& re : next_result) {
                                            uint64_t r_next;
                                            Z3_get_numeral_uint64(m_ctx, re, &r_next);
                                            bs_v.emplace_back(_bs{ r_next ,_next, False });
                                        }
                                    }
                                    if (traceState) std::cout << "Fork at: " << std::hex << guest_start << "  {" << std::endl;
                                    for (auto&& _bs : bs_v) {
                                        State* state = newForkState(_bs.addr);
                                        branch.emplace_back(state);
                                        state->add_assert(guard.translate(*state), _bs._not);
                                        if (_bs._s_addr) {
                                            auto _next_a = Vns(state->m_ctx, Z3_translate(m_ctx, _bs._s_addr, *state));
                                            auto _next_b = Vns(state->m_ctx, Z3_mk_unsigned_int64(state->m_ctx, _bs.addr, Z3_get_sort(state->m_ctx, _next_a)));
                                            state->add_assert_eq(_next_a, _next_b);
                                        }
                                        if (traceState) std::cout << "    +++++++++++++++ push : " << std::hex << state->get_cpu_ip() << " +++++++++++++++" << std::endl;
                                    }
                                    if (traceState) std::cout << " } Fork end" << std::endl;
                                    status = Fork; goto EXIT;
                                }
                                else {
                                    status = Death; goto EXIT;
                                }
                            }
                        }
                        case Ist_NoOp: break;
                        case Ist_IMark: {
                            guest_start = (ADDR)s->Ist.IMark.addr;
                            if (this->is_dynamic_block) {
                                this->is_dynamic_block = false;
                                goto For_Begin;// fresh changed block
                            }
                            break;
                        };
                        case Ist_AbiHint:break; //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
                        case Ist_PutI: {
                            //PutI(840:8xI8)[t10,-1]
                            //840:arr->base
                            //8x :arr->nElems
                            //I8 :arr->elemTy
                            //t10:ix
                            //-1 :e->Iex.GetI.bias
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
                            IRDirty* dirty = s->Ist.Dirty.details;
                            auto guard = tIRExpr(dirty->guard);
                            auto k = CCall(dirty->cee, dirty->args, Ity_I64);
                            if (dirty->tmp != -1 && (UChar)guard) {
                                irTemp[dirty->tmp] = k;
                                if (NEED_CHECK)std::cout << k << std::endl;
                            }
                            break;
                        }

                        case Ist_LoadG: {
                            IRLoadG* lg = s->Ist.LoadG.details;
                            auto guard = tIRExpr(lg->guard);
                            if (guard.real()) {
                                irTemp[lg->dst] = (((UChar)guard)) ? ILGop(lg) : tIRExpr(lg->alt);
                            }
                            else {
                                irTemp[lg->dst] = ite(guard == 1, ILGop(lg), tIRExpr(lg->alt));
                            }
                            if (NEED_CHECK)std::cout << irTemp[lg->dst] << std::endl;
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
                                mem.Ist_Store(addr, ite(guard == 1, mem.Iex_Load(addr, length2ty(data.bitn)), data));
                            }
                            break;
                        }
                        case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/
                        case Ist_LLSC:
                        default:
                            vex_printf("what ppIRStmt %d\n", s->tag);
                            vpanic("what ppIRStmt");
                        }
                        if (NEED_CHECK)
                            if (s->tag != Ist_WrTmp) { vex_printf("\n"); }
                    }
                    switch (irsb->jumpkind) {
                    case Ijk_Boring:		break;
                    case Ijk_Call:			break;
                    case Ijk_Ret:           break;
                    case Ijk_SigTRAP: {
                    bkp_pass:
                        auto _where = CallBackDict.lower_bound((ADDR)guest_start);
                        if (_where != CallBackDict.end()) {
                            if (hook_bkp) {
                                guest_start = hook_bkp;
                                hook_bkp = NULL;
                                goto For_Begin;
                            }
                            else {
                                if (!is_first_bkp_pass) {
                                    if (_where->second.cb) {
                                        status = (_where->second.cb)(this);//State::delta maybe changed by callback
                                    }
                                    if (status != Running) {
                                        goto EXIT;
                                    }
                                }
                                else {
                                    is_first_bkp_pass = False;
                                }
                                if (delta) {
                                    guest_start = guest_start + delta;
                                    delta = 0;
                                    goto For_Begin;
                                }
                                else {
                                    __m256i m32 = mem.Iex_Load<Ity_V256>(guest_start);
                                    m32.m256i_i8[0] = _where->second.original;
                                    pap.start_swap = 2;
                                    vta.guest_bytes = (UChar*)(&m32);
                                    vta.guest_bytes_addr = (Addr64)((ADDR)guest_start);
                                    auto max_insns = pap.guest_max_insns;
                                    pap.guest_max_insns = 1;
                                    irsb = LibVEX_FrontEnd(&vta, &res, &pxControl);
                                    //ppIRSB(irsb);
                                    pap.guest_max_insns = max_insns;
                                    hook_bkp = (ADDR)guest_start + irsb->stmts[0]->Ist.IMark.len;
                                    irsb->jumpkind = Ijk_SigTRAP;
                                    goto For_Begin_NO_Trans;
                                }
                            }
                        }
                    }
                                    /*Ijk_Sys_syscall, Ijk_NoDecode, Ijk_ClientReq,Ijk_Yield, Ijk_EmWarn, Ijk_EmFail, Ijk_MapFail, Ijk_InvalICache,
                                    Ijk_FlushDCache, Ijk_NoRedir, Ijk_SigILL, Ijk_SigSEGV, Ijk_SigBUS, Ijk_SigFPE, Ijk_SigFPE_IntDiv, Ijk_SigFPE_IntOvf,
                                    Ijk_Sys_int32,Ijk_Sys_int128, Ijk_Sys_int129, Ijk_Sys_int130, Ijk_Sys_int145, Ijk_Sys_int210, Ijk_Sys_sysenter:*/
                    default:
                        status = Ijk_call(irsb->jumpkind);
                        if (status != Running) {
                            goto EXIT;
                        }
                        if (delta) {
                            guest_start = guest_start + delta;
                            delta = 0;
                            goto For_Begin;
                        }
                    }
                Isb_next:
                    Vns next = tIRExpr(irsb->next);
                    if (next.real()) {
                        guest_start = next;
                    }
                    else {
                        std::vector<Z3_ast> result;
                        switch (eval_all(result, solv, next)) {
                        case 0: next.~Vns(); goto EXIT;
                        case 1:
                            uint64_t u64_Addr;
                            Z3_get_numeral_uint64(m_ctx, result[0], &u64_Addr);
                            guest_start = u64_Addr;
                            Z3_dec_ref(m_ctx, result[0]);
                            break;
                        default:
                            if (traceState) std::cout << "Fork at: " << std::hex << guest_start << "  {" << std::endl;
                            for (auto&& re : result) {
                                uint64_t rgurd;
                                Z3_get_numeral_uint64(m_ctx, re, &rgurd);

                                State* state = newForkState(rgurd);
                                branch.emplace_back(state);

                                state->add_assert_eq(Vns(m_ctx, Z3_translate(m_ctx, re, *state)), next.translate(*state));
                                if (traceState) std::cout << "    +++++++++++++++ push : " << std::hex << state->get_cpu_ip() << " +++++++++++++++" << std::endl;
                                Z3_dec_ref(m_ctx, re);
                            }
                            status = Fork;
                            next.~Vns(); // check it
                            if (traceState) std::cout << " } Fork end" << std::endl;
                            goto EXIT;
                        }
                    }
                };

            }
            catch (...) {
                //SEH Exceptions (/EHa)
                try {
                    cpu_exception();
                    if (status = Death) {
                        std::cout << "W MEM ERR at " << std::hex << guest_start << std::endl;
                        status = Death;
                    }
                }
                catch (...) {
                    std::cout << "W MEM ERR at " << std::hex << guest_start << std::endl;
                    status = Death;
                }
            }
        }
        catch (exception & error) {
            vex_printf("unexpected z3 error: at %llx\n", guest_start);
            std::cout << error << std::endl;
            status = Death;
        }

        if (status == Exception) {
            status = Running;
            goto Begin_try;
        }


    EXIT:
        unit_lock = true;
        thread_unregister();
    }

    State_Tag Ijk_call(IRJumpKind kd) {
        switch (kd) {
        case Ijk_Sys_syscall:
            return Sys_syscall();
        default:
            return Death;
        }
    }

    State_Tag Sys_syscall() {
        UChar rax = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rax);
        ULong rdi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rdi);
        ULong rdx = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rdx);
        ULong rsi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rsi);
        switch (rax) {
        case 0:// input
            if (rdi == 0) {
                for (ULong n = 0; n < rdx; n++) {
                    if (flag_count >= flag_max_count) {
                        mem.Ist_Store(rsi + n, '\n');
                    }
                    else {
                        Vns FLAG = get_int_const(8);
                        mem.Ist_Store(rsi + n, FLAG);
                        auto ao1 = FLAG >= 'A' && FLAG <= 'Z';
                        auto ao2 = FLAG >= 'a' && FLAG <= 'z';
                        auto ao3 = FLAG >= '0' && FLAG <= '9';
                        add_assert(ao1|| ao2|| ao3, True);
                    }
                }
                regs.Ist_Put(AMD64_IR_OFFSET::rax, rdx);
                flag_count += rdx;
                return Running;
            }
        case 1:
            for (ULong n = 0; n < rdx; n++) {
                UChar chr = mem.Iex_Load<Ity_I8>(rsi + n);
                vex_printf("%c", chr);
            }
            regs.Ist_Put(AMD64_IR_OFFSET::rax, rdx);
            return Running;
        }


        return Death;
    }
};








State_Tag avoid_ret(State *s) {
    Regs::X86 reg(*s);
    Vns esi = reg.guest_ESI;
    std::cout << esi << std::endl;
    return Death;
}

State_Tag avoid_ret2(State *s) {
    Regs::X86 reg(*s);
    Vns guest_EDX = reg.guest_EDX;
    Vns guest_EBX = reg.guest_EBX;
    std::cout << guest_EDX<< guest_EBX << std::endl;
    return Death;
}



State_Tag success_ret(State* s) {
    s->solv.push();
    auto ecx = s->regs.Iex_Get<Ity_I32>(12);
    auto edi = s->regs.Iex_Get<Ity_I32>(36);

    for (int i = 0; i < 44; i++) {
        auto al = s->mem.Iex_Load<Ity_I8>(ecx + i);
        auto bl = s->mem.Iex_Load<Ity_I8>(edi + i);
        s->add_assert_eq(al, bl);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == sat) {
        vex_printf("sat");
        auto m = s->solv.get_model();
        std::cout << m << std::endl;
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    s->solv.pop();
    return Death;
}





#include "SimulationEngine/Z3_Target_Call/Guest_Helper.hpp"

Vns flag_limit(Vns &flag) {
    char flags_char[] = "@_-{}1:() ^";
    Vns re = Vns(flag, flags_char[0]) == flag;
    for (int i = 1; i < sizeof(flags_char); i++) {
        re = re || (Vns(flag, flags_char[i]) == flag);
    }
    auto ao1 = flag >= 'a' && flag <= 'z';
    auto ao2 = flag >= 'A' && flag <= 'Z';
    auto ao3 = flag >= '0' && flag <= '9';
    return re || ao1 || ao2 || ao3;
}


#include "example.hpp"



State_Tag finall(State* s) {
    context& c = *s;
    s->solv.push();

    Regs::X86 reg(*s);
    Vns eax = reg.guest_EAX;
    Vns ebx = reg.guest_EBX;
    Vns ecx = reg.guest_ECX;
    Vns edi = reg.guest_EDI;
    for (int i = 0; i < 10; i++) {
        auto e = s->mem.Iex_Load<Ity_I32>(ecx + i*4);
        s->add_assert_eq(e, s->mem.Iex_Load<Ity_I32>(edi + i * 4));
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == sat) {
        vex_printf("sat");
        auto m = s->solv.get_model();
        std::cout << m << std::endl;
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    s->solv.pop();
    return Death;
}



State_Tag finall2(State* s) {
    Regs::X86 reg(*s);
    auto v = s->mem.Iex_Load<Ity_I32>((Vns)reg.guest_EBP - 0x1c);
    if ((UChar)v == 5)
        return (State_Tag)2333;
    else if ((UChar)v == 100) {
        printf("fgbfgfgbfg");
    }
    else {
        return Running;
    }
}

State_Tag checkme(State* s) {
    Regs::X86 reg(*s);
    auto v = s->mem.Iex_Load<Ity_I32>((Vns)reg.guest_EBP - 0x1c);

    auto df=s->mem.getMemPage(0x5671A3);

    return Running;
}



int main() {

    flag_max_count = 84;
    flag_count = 0;



    DebugState state(INIFILENAME, (Addr64)NULL, True);
    context& c = state;


    expr re =concat(c.bv_val(0x666, 128), c.bv_val(0x2333, 128));


    Vns(re).simplify();

    auto sd = &state;
    State::pool->enqueue([sd] {
        sd->start(True);
        });
    TESTCODE(
        State::pool->wait();
    )

    
    std::cout << *sd << std::endl;

    

    
    printf("OVER");
    getchar();
    return 0;
}




