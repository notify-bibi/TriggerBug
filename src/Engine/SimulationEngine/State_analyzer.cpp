#include "State_analyzer.hpp"


void StateAnalyzer::Run() {
    State* s = &m_state;
    State::pool->enqueue([s] {
        s->start(True);
        });
    TESTCODE(
        State::pool->wait();
    );
    analyze(s, true);
}

void GraphView::analyze(Bool first_bkp_pass)
{
    if (this->status != NewState) {
        vex_printf("this->status != NewState");
        return;
    }
    Bool is_first_bkp_pass = False;
    Addr64 hook_bkp = NULL;
    thread_register();
    t_index = temp_index();
    Vns* irTemp = ir_temp[t_index];
    this->is_dynamic_block = false;

Begin_try:

    if (first_bkp_pass)
        if ((UChar)mem.Iex_Load<Ity_I8>(guest_start) == 0xCC) {
            is_first_bkp_pass = True;
            goto bkp_pass;
        }
    for (;;) {
    For_Begin:
        IRSB* irsb = BB2IR();
        guest_start_of_block = guest_start;
    For_Begin_NO_Trans:
        for (UInt stmtn = 0; stmtn < irsb->stmts_used; stmtn++) {
            IRStmt* s = irsb->stmts[stmtn];
            switch (s->tag) {
            case Ist_Put: {
                if (RegsIpOffset == s->Ist.Put.offset) {
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
                Vns guard = tIRExpr(s->Ist.Exit.guard);
                s->Ist.Exit.dst->Ico.U64;
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

                break; //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
            }
            case Ist_PutI: {
            }
            case Ist_Dirty: {
            }

            case Ist_LoadG: {
            }
            case Ist_StoreG: {
            }
            case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/
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
                    
        }
    };
            


EXIT:
    unit_lock = true;
    thread_unregister();
}
