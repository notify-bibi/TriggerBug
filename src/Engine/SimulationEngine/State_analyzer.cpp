#include "State_analyzer.hpp"

void StateAnalyzer::Run() {
    State* s = &m_state;
    State::pool->enqueue([s] {
        s->start(True);
        });
    TESTCODE(
        State::pool->wait();
    );
    analyze(m_state
    );
}


IRSB* GraphView::BB2IR() {
    mem.set_double_page(guest_start, pap);
    pap.start_swap = 0;
    m_state.vta->guest_bytes = (UChar*)(pap.t_page_addr);
    m_state.vta->guest_bytes_addr = (Addr64)((ADDR)guest_start);
    VexRegisterUpdates pxControl;
    VexTranslateResult res;
    return LibVEX_FrontEnd(m_state.vta, &res, &pxControl);
}

static UInt mk_key(Int offset, IRType ty)
{
    /* offset should fit in 16 bits. */
    UInt minoff = offset;
    UInt maxoff = minoff + sizeofIRType(ty) - 1;
    vassert((minoff & ~0xFFFF) == 0);
    vassert((maxoff & ~0xFFFF) == 0);
    return (minoff << 16) | maxoff;
}

IRExpr* Vns2Con(Vns const& v) {
    IRExpr* r = IRExpr_Const(IRConst_U64(v));
    r->Iex.Const.con->tag = v;
    return r;
}

//
//
//
//IRExpr* find_IRExpr(context &m_ctx, IRSB*bb, UInt idx, IRExpr* e) {
//    switch (e->tag) {
//    case Iex_Get: { 
//        return find_stmt(m_ctx, bb, idx - 1, e);
//    }
//    case Iex_RdTmp: { 
//        return find_stmt(m_ctx, bb, idx - 1, e);
//    }
//    case Iex_Unop: {
//        IRExpr* arg = find_IRExpr(m_ctx, bb, idx, e->Iex.Unop.arg);
//        if (arg->tag == Iex_Const) {
//            Vns simp = State::T_Unop(m_ctx, e->Iex.Unop.op, Vns(m_ctx, arg->Iex.Const.con));
//            if (simp.bitn <= 64) {
//                return Vns2Con(simp);
//            }
//            return e;
//        }
//        return;
//    }
//    case Iex_CCall: 
//    case Iex_GSPTR: {
//    };
//    case Iex_VECRET:
//    case Iex_Binder:
//    case Iex_Const: return e;;
//    default:
//        vex_printf("tIRExpr error:  %d", e->tag);
//        vpanic("not support");
//    }
//
//    
//}
//
//
//
//
//IRExpr* find_stmt(context& m_ctx, IRSB* bb, UInt idx, IRExpr* e) {
//    switch (e->tag) {
//    case Iex_Get: {
//        for (UInt stmtn = idx; stmtn >= 0; stmtn--) {
//            IRStmt* st = bb->stmts[stmtn];
//            if (st->tag = Ist_Put) {
//                UInt gm = e->Iex.Get.offset + sizeofIRType(e->Iex.Get.ty) - 1;
//                IRType ty = typeOfIRExpr(bb->tyenv, st->Ist.Put.data);
//                UInt pm = st->Ist.Put.offset + sizeofIRType(ty) - 1;
//                if (gm >= st->Ist.Put.offset && e->Iex.Get.offset <= pm) {
//                    if (gm == pm && st->Ist.Put.offset == e->Iex.Get.offset) {
//                        return st->Ist.Put.data;
//                    }
//                    //need
//                }
//            }
//        }
//        break;
//    }
//    case Iex_RdTmp: {
//        for (UInt stmtn = idx; stmtn >= 0; stmtn--) {
//            IRStmt* st = bb->stmts[stmtn];
//            if (st->tag = Ist_WrTmp) {
//                if (e->Iex.RdTmp.tmp == st->Ist.WrTmp.tmp) {
//                    return st->Ist.WrTmp.data;
//                }
//            }
//        }
//        break;
//    }
//    case Iex_Load: {
//
//
//
//    }
//    case Iex_Unop: {
//
//    }
//    case Iex_CCall: {
//
//    }
//    case Iex_Binop: { }
//    case Iex_Triop: {  }
//    case Iex_Qop: {  }
//    case Iex_Const: {  }
//    case Iex_ITE: { }
//    case Iex_GetI: {};
//    case Iex_GSPTR: { };
//    case Iex_VECRET:
//    case Iex_Binder:
//    default:
//        vex_printf("tIRExpr error:  %d", e->tag);
//        vpanic("not support");
//    };
//    return e;
//}
//
//
//inline IRExpr* GraphView::tIRExpr(IRExpr* e)
//{
//    switch (e->tag) {
//    case Iex_Get: { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
//    case Iex_RdTmp: { return  irTemp[e->Iex.RdTmp.tmp]; }
//    case Iex_Unop: { return IRExpr_Unop(e->Iex.Unop.op, tIRExpr(e->Iex.Unop.arg)); }
//    case Iex_Binop: { return IRExpr_Binop(e->Iex.Binop.op, tIRExpr(e->Iex.Binop.arg1), tIRExpr(e->Iex.Binop.arg2)); }
//    case Iex_Triop: { return IRExpr_Triop(e->Iex.Triop.details->op, tIRExpr(e->Iex.Triop.details->arg1), tIRExpr(e->Iex.Triop.details->arg2), tIRExpr(e->Iex.Triop.details->arg3)); }
//    case Iex_Qop: { return IRExpr_Qop(e->Iex.Qop.details->op, tIRExpr(e->Iex.Qop.details->arg1), tIRExpr(e->Iex.Qop.details->arg2), tIRExpr(e->Iex.Qop.details->arg3), tIRExpr(e->Iex.Qop.details->arg4)); }
//    case Iex_Load: {
//       // return mem.Iex_Load(tIRExpr(e->Iex.Load.addr), e->Iex.Get.ty); 
//    }
//    case Iex_Const: { return e; }
//    case Iex_ITE: { return IRExpr_ITE(tIRExpr(e->Iex.ITE.cond), tIRExpr(e->Iex.ITE.iftrue), tIRExpr(e->Iex.ITE.iffalse)); }
//    case Iex_CCall: { 
//        IRExpr** args2 = shallowCopyIRExprVec(e->Iex.CCall.args);
//        for (Int i = 0; args2[i]; i++) {
//            args2[i] = tIRExpr(args2[i]);
//        }
//        return  IRExpr_CCall(e->Iex.CCall.cee, e->Iex.CCall.retty, args2);
//    }
//    case Iex_GetI: {
//        auto ix = tIRExpr(e->Iex.GetI.ix); 
//        return regs.Iex_Get(e->Iex.GetI.descr->base + (((UInt)(e->Iex.GetI.bias + (int)(ix))) % e->Iex.GetI.descr->nElems) * ty2length(e->Iex.GetI.descr->elemTy), e->Iex.GetI.descr->elemTy);
//    };
//    case Iex_GSPTR: {
//        return e;
//    };
//    case Iex_VECRET:
//    case Iex_Binder:
//    default:
//        vex_printf("tIRExpr error:  %d", e->tag);
//        vpanic("not support");
//    }
//}
void GraphView::analyze(ADDR block_oep)
{
    guest_start = block_oep;
    Bool is_first_bkp_pass = False;
    Addr64 hook_bkp = 0;
    State::thread_register();
    t_index = temp_index();

Begin_try:
    struct RegKey
    {
        UInt k;
        IRExpr* data;
        IRExpr* guard;
    };


    std::vector<RegKey> regKey;
    IRExpr* exp;
    //for (;;) {
    //    IRSB* irsb = BB2IR();
    //    ppIRSB(irsb);
    //    for (UInt stmtn = irsb->stmts_used - 1; stmtn >= 0; stmtn--) {
    //        IRStmt* s = irsb->stmts[stmtn];
    //        switch (s->tag) {
    //        case Ist_Put: { regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
    //        case Ist_Store: {  };
    //        case Ist_WrTmp: { irTemp[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data); break; };
    //        case Ist_CAS: {
    //            break;
    //        }
    //        case Ist_Exit: {
    //            break;
    //        }
    //        case Ist_NoOp: break;
    //        case Ist_IMark: {
    //            guest_start = (ADDR)s->Ist.IMark.addr;
    //            break;
    //        };
    //        case Ist_AbiHint: //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
    //            break;
    //        case Ist_PutI: {
    //            auto ix = tIRExpr(s->Ist.PutI.details->ix);
    //            break;
    //        }
    //        case Ist_Dirty: {
    //            IRDirty* dirty = s->Ist.Dirty.details;
    //            auto guard = tIRExpr(dirty->guard);
    //            if (((UChar)guard) & 1) {
    //            }
    //            break;
    //        }
    //        case Ist_LoadG: {
    //            IRLoadG* lg = s->Ist.LoadG.details;
    //            auto guard = tIRExpr(lg->guard);
    //            break;
    //        }
    //        case Ist_StoreG: {
    //            break;
    //        }
    //        case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/
    //        case Ist_LLSC:
    //        default: {
    //            vex_printf("what ppIRStmt %d\n", s->tag);
    //            vpanic("what ppIRStmt");
    //        }
    //        }

    //    }
    //    switch (irsb->jumpkind) {
    //    case Ijk_Boring:		break;
    //    case Ijk_Call:			break;
    //    case Ijk_Ret:           break;
    //    case Ijk_SigTRAP: {}
    //    default:
    //    }
    //Isb_next:
    //    IRExpr* next = tIRExpr(irsb->next);
    //    
    //};

EXIT:
    State::thread_unregister();
}
