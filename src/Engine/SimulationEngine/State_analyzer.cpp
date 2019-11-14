#include "State_analyzer.hpp"


void StateAnalyzer::Run() {
    State* s = &m_state;
    State::pool->enqueue([s] {
        s->start(True);
        });
    TESTCODE(
        State::pool->wait();
    );
    analyze(m_state, true);
}

inline Vns GraphView::tIRExpr(IRExpr* e)
{
    switch (e->tag) {
    case Iex_Get: { }
    case Iex_RdTmp: { }
    case Iex_Unop: { }
    case Iex_Binop: { }
    case Iex_Triop: { }
    case Iex_Qop: { }
    case Iex_Load: {  }
    case Iex_Const: { return Vns(m_ctx, e->Iex.Const.con); }
    case Iex_ITE: { }
    case Iex_CCall: { }
    case Iex_GetI: { };
    case Iex_GSPTR: { };
    case Iex_VECRET: { }
    case Iex_Binder: { }
    default:
        vex_printf("tIRExpr error:  %d", e->tag);
        vpanic("not support");
    }
}


IRSB* GraphView::BB2IR() {
    VexTranslateResult res;
    mem.set_double_page(guest_start, pap);
    pap.start_swap = 0;
    m_state.vta.guest_bytes = (UChar*)(pap.t_page_addr);
    m_state.vta.guest_bytes_addr = (Addr64)((ADDR)guest_start);
    return LibVEX_FrontEnd(&m_state.vta, &res, &m_state.pxControl);
}

void GraphView::analyze(ADDR block_oep, Bool first_bkp_pass)
{
    guest_start = block_oep;

    Bool is_first_bkp_pass = False;
    Addr64 hook_bkp = NULL;
    State::thread_register();
    t_index = temp_index();
    Vns* irTemp = State::ir_temp[t_index];
    is_dynamic_block = false;

Begin_try:

    if (first_bkp_pass)
        if ((UChar)m_state.mem.Iex_Load<Ity_I8>(guest_start) == 0xCC) {
            is_first_bkp_pass = True;
            goto bkp_pass;
        }
    for (;;) {
    For_Begin:
        IRSB* irsb = BB2IR();
        ppIRSB(irsb);
    For_Begin_NO_Trans:
        for (UInt stmtn = 0; stmtn < irsb->stmts_used; stmtn++) {
            IRStmt* s = irsb->stmts[stmtn];
            switch (s->tag) {
            case Ist_Put: {
                if (m_state.gRegsIpOffset() == s->Ist.Put.offset) {
                    Vns regData = tIRExpr(s->Ist.Put.data);
                }
                break; 
            }
            case Ist_Store: {
                break;
            };
            case Ist_WrTmp: {
                break;
            }
            case Ist_CAS: {
                break;
            }
            case Ist_Exit: {
                //new Block(guest_start_ep, guest_start);
                //new Block(s->Ist.Exit.dst->Ico.U64, );
                

                if (s->Ist.Exit.jk != Ijk_Boring
                    && s->Ist.Exit.jk != Ijk_Call
                    && s->Ist.Exit.jk != Ijk_Ret
                    )
                {
                }
                else {
                    guest_start = s->Ist.Exit.dst->Ico.U64;
                    hook_bkp = NULL;
                    goto For_Begin;
                }
            }
            case Ist_NoOp: break;
            case Ist_IMark: {
                guest_start = (ADDR)s->Ist.IMark.addr;
                break;
            };
            case Ist_AbiHint:{
                break;
            }
            case Ist_PutI: {
            }
            case Ist_Dirty: {
            }

            case Ist_LoadG: {
            }
            case Ist_StoreG: {
            }
            case Ist_MBE:
            case Ist_LLSC:
            default:
                vex_printf("what ppIRStmt %d\n", s->tag);
                vpanic("what ppIRStmt");
            }
        }
        switch (irsb->jumpkind) {
        case Ijk_Boring:		break;
        case Ijk_Call:			break;
        case Ijk_Ret:           break;
        case Ijk_SigTRAP: {
        bkp_pass:
            auto _where = State::CallBackDict.lower_bound((ADDR)guest_start);
            if (_where != State::CallBackDict.end()) {
                if (hook_bkp) {
                    guest_start = hook_bkp;
                    hook_bkp = NULL;
                    goto For_Begin;
                }
                else {
                    if (!is_first_bkp_pass) {
                        if (_where->second.cb) {
                            //m_state.status = (_where->second.cb)(this);//State::delta maybe changed by callback
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
                        m_state.vta.guest_bytes = (UChar*)(&m32);
                        m_state.vta.guest_bytes_addr = (Addr64)((ADDR)guest_start);
                        auto max_insns = pap.guest_max_insns;
                        pap.guest_max_insns = 1;
                        irsb = LibVEX_FrontEnd(&m_state.vta, &m_state.res, &m_state.pxControl);
                        //ppIRSB(irsb);
                        pap.guest_max_insns = max_insns;
                        hook_bkp = (ADDR)guest_start + irsb->stmts[0]->Ist.IMark.len;
                        irsb->jumpkind = Ijk_SigTRAP;
                        goto For_Begin_NO_Trans;
                    }
                }
            }
        }
        default:
            
        }
    Isb_next:
        Vns next = tIRExpr(irsb->next);
        if (next.real()) {
            guest_start = next;
        }
        else {
                    
        }
    };

EXIT:
    State::thread_unregister();
}
