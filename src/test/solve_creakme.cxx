#include "test.h"
#include <forward_list>
extern "C" {
    #include <ir_opt.h>
}

#include "engine/irsb_cache.h"
using namespace TR;




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

rsval<Long> symbolic_read(StateBase &s, const rsval<ULong>& addr, const rsval<Long>& count) {
    int n = 0;
    for (; n < 10; n++) {
        auto FLAG = s.mk_int_const(8).tos<false, 8>();
        s.mem.Ist_Store(addr + n, FLAG);
        auto ao1 = FLAG >= 'A' && FLAG <= 'Z';
        auto ao2 = FLAG >= 'a' && FLAG <= 'z';
        auto ao3 = FLAG >= '0' && FLAG <= '9';
        auto ao4 = FLAG == 0xD || FLAG == 0xA;
        s.solv.add_assert(ao1 || ao2 || ao3 || ao4);
    }
    auto res_count = s.mk_int_const(8).tors<false, 8>();
    s.solv.add_assert( (res_count < 12).tos() );
    return res_count;
}
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
            Int i;
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



class GraphView {
    using _jmps = std::forward_list<Addr>;
    template<typename Addr> friend class PathExplorer;

    spin_mutex translate_mutex;
    typedef struct blockEnd {
        IRJumpKind kd;
        Addr addr;
    };
    typedef enum { Loop_INVALID, Loop_True, Loop_False } loop_kind;
    typedef struct jmp_info {
        Addr addr;
        loop_kind loop;
    };
    using ast_block = std::shared_ptr<AstBlock>;
    using jmps = _jmps;
    using jmp_kind = std::forward_list<jmp_info>;
    std::map<Addr, jmp_kind> m_jmp;
    std::map<Addr, _jmps> m_in;
    std::map<Addr, ast_block> m_block_begin;
    std::map<Addr, blockEnd>  m_block_end;
    ThreadPool m_pool;


    void _add_block(irsb_chunk irsb_chunk) {



    }

    Addr prev_code_addr(IRSB* irsb, Addr addr, Addr this_code) {
        IRStmt* s = irsb->stmts[0];
        for (UInt stmtn = 0; stmtn < irsb->stmts_used;
            s = irsb->stmts[++stmtn])
        {
            if (s->tag == Ist_IMark && s->Ist.IMark.addr + s->Ist.IMark.len >= this_code) {
                return s->Ist.IMark.addr;
            }
        }
        return 0;
    }

    void add_block(irsb_chunk irsb_chunk, IRJumpKind kd) {
        Addr block_start = irsb_chunk->get_bb_base();
        Addr block_end = block_start + irsb_chunk->get_bb_size() - 1;
        if (kd == Ijk_SigSEGV) return;
        spin_unique_lock lock(translate_mutex);
        std::map<Addr, blockEnd>::iterator it = m_block_end.find(block_end);
        /*if (0x00007ffff7a8d33d == block_start||0x00007ffff7a8d34a == block_start) {
            printf("");
        }*/
        if (it != m_block_end.end()) {
            if (block_start > it->second.addr) {
                Addr nEnd = prev_code_addr(nullptr, it->second.addr, block_start);
                //m_block_begin[it->second.addr] = nEnd;
                //m_block_begin.insert(std::make_pair(it->second.addr, nEnd));
                _jmp_to_no_mutex(nEnd, block_start);
                m_block_end[nEnd] = blockEnd{ Ijk_Boring, it->second.addr };
                m_block_begin[block_start] = std::make_shared<AstBlock>(irsb_chunk);
#ifdef OUTPUT
                printf("update block %p   %p \n", it->second.addr, nEnd);
#endif
                it->second.addr = block_start;
            }
            else if (block_start < it->second.addr) {
                block_end = prev_code_addr(nullptr, block_start, it->second.addr);
                kd = Ijk_Boring;
                if (!block_end) {
                    vassert(0);
                }
                _jmp_to_no_mutex(block_end, it->second.addr);
                vassert(block_start <= block_end);
                vassert(block_end < it->second.addr);
                goto NewBlock;
            }
        }
        else {
        NewBlock:
            m_block_end[block_end] = blockEnd{ kd, block_start };
            m_block_begin[block_start] = std::make_shared<AstBlock>(irsb_chunk);
#ifdef OUTPUT
            printf("new block %p   %p \n", block_start, block_end);
#endif
        }

    }

    void explore_block(Addr& block_task, Addr block_start) {
        if (block_task) {
            enqueue(block_start);
        }
        else {
            block_task = block_start;
        }
    }

    void enqueue(Addr block_start) {
        if (!getEnd(block_start))
        {
        }
    }

    void _jmp_to(Addr from, Addr to) {
        spin_unique_lock lock(translate_mutex);
        _jmp_to_no_mutex(from, to);
    }

    inline  void _jmp_to_no_mutex(Addr from, Addr to) {
        if (from == 0) {
            vassert(0);
        }
#ifdef OUTPUT
        printf("_jmp_to %p   %p \n", from, to);
#endif
        std::map<Addr, jmp_kind>::iterator it = m_jmp.find(from);
        if (it == m_jmp.end()) {
            m_jmp[from] = jmp_kind{ jmp_info{to, Loop_INVALID } };
        }
        else {
            it->second.push_front(jmp_info{ to, Loop_INVALID });
        }

        std::map<Addr, _jmps>::iterator it_in = m_in.find(to);
        if (it_in == m_in.end()) {
            m_in[to] = _jmps{ from };
        }
        else {
            it_in->second.push_front(from);
        }
    }

    Addr getBegin(Addr block_end) {
        std::map<Addr, blockEnd>::iterator it = m_block_end.find(block_end);
        if (it == m_block_end.end()) { return 0; }
        return it->second.addr;
    }

    Addr getEnd(Addr block_begin) {
        std::map<Addr, ast_block>::iterator it = m_block_begin.find(block_begin);
        if (it == m_block_begin.end()) { return 0; }
        //return it->second;
    }


public:
    GraphView() :m_pool(2) {
    }
    void wait() { m_pool.wait(); }

    void explore_block(Addr block_start) {
        /*std::map<Addr, Addr>::iterator it = m_block_begin.find(block_start);
        if (it != m_block_begin.end()) return;
        enqueue(block_start);*/
    }

    void add_jmp(Addr from, Addr to) {
        _jmp_to(from, to);
        explore_block(to);
    }



    Addr begin2End(Addr block_begin) {
        //std::map<Addr, Addr>::iterator ait = m_block_begin.find(block_begin);
        //if (ait == m_block_begin.end()) {
        //    if (0x00007ffff7a8d34a == block_begin) {
        //        printf("");
        //    }
        //    m_pool.enqueue(
        //        [this, block_begin] {
        //            _add_block(block_begin);
        //        }
        //    );
        //    wait();
        //}
        //std::map<Addr, Addr>::iterator it = m_block_begin.find(block_begin);
        //if (it == m_block_begin.end()) {
        //    return 0;
        //}
        //return it->second;
    }

};


class explorer : public TraceInterface {
    GraphView& m_gv;
public:
    explorer(GraphView& gv) :m_gv(gv) {

    }

    virtual void traceStart(State& s, HWord ea) override;
    virtual void traceIRSB(State& s, HWord ea, irsb_chunk&) override;
    virtual void traceIRStmtStart(State& s, const IRSB* irsb, UInt stmtn) override;
    virtual void traceIRStmtEnd(State& s, const IRSB* irsb, UInt stmtn) override;
    virtual void traceIRnext(State& s, const IRSB* irsb, const tval& next) override;
    virtual void traceIrsbEnd(State& s, irsb_chunk&) override;
    virtual void traceFinish(State& s, HWord ea) override;

    virtual TraceInterface* mk_new_TraceInterface() override { return new explorer(m_gv); }
    virtual ~explorer() {}
};


void explorer::traceStart(State& s, HWord ea)
{
    TraceInterface::traceStart(s, ea);
}

void explorer::traceIRSB(State& s, HWord ea, irsb_chunk& irsb)
{
    TraceInterface::traceIRSB(s, ea, irsb);
    //m_gv.add_block(irsb)

   // AstBlock ab(irsb);
    //ppIRSB(irsb->get_irsb());
}

void explorer::traceIRStmtStart(State& s, const IRSB* irsb, UInt stmtn)
{
    TraceInterface::traceIRStmtStart(s, irsb, stmtn);
}

void explorer::traceIRStmtEnd(State& s, const IRSB* irsb, UInt stmtn)
{
    TraceInterface::traceIRStmtEnd(s, irsb, stmtn);
}

void explorer::traceIRnext(State& s, const IRSB* irsb, const tval& next)
{
    TraceInterface::traceIRnext(s, irsb, next);
}

void explorer::traceIrsbEnd(State& s, irsb_chunk& irsb)
{
    TraceInterface::traceIrsbEnd(s, irsb);
}

void explorer::traceFinish(State& s, HWord ea)
{
    TraceInterface::traceFinish(s, ea);
}

//class Block : ref_manager {
//    Addr m_sea; // start
//    Addr m_eea; // end
//    std::deque<sv::tval> m_param;
//    using nextTy = std::pair<sbool, ref<Block>>;
//    std::deque<nextTy> m_conditional;
//
//public:
//    Block(Addr sea, Addr eea) :m_sea(sea), m_eea(eea) {
//        
//
//    }
//
//
//
//
//
//};


extern "C" void libvex_BackEnd(const VexTranslateArgs * vta,
    /*MOD*/ VexTranslateResult * res,
    /*MOD*/ IRSB * irsb,
    VexRegisterUpdates pxControl);


auto emu_one_irsb(Addr &guest_start, std::deque<TR::State::BtsRefType>& tmp_branch, TR::State_Tag& m_status, State& s, irsb_chunk irsb) {
    Vex_Kind vkd;
    //ppIRSB(irsb);
    s.get_trace()->traceIRSB(s, guest_start, irsb);
    if (s.vinfo().is_mode_32()) {
        vkd = s.emu_irsb<32>(tmp_branch, guest_start, m_status, irsb->get_irsb());
    }
    else {
        vkd = s.emu_irsb<64>(tmp_branch, guest_start, m_status, irsb->get_irsb());
    }
    s.get_trace()->traceIrsbEnd(s, irsb);
    return vkd;
}


void gk(State&s, Addr ea, GraphView& gv) {
    
    
    s.get_trace()->setFlags(CF_traceJmp);
    s.get_trace()->setFlags(CF_ppStmts);
    //s.vctx().hook_add(0x551AF328, nullptr, CF_ppStmts);
    Addr ip = ea;
    Vex_Kind vkd;
    std::deque<TR::State::BtsRefType> tmp_branch = s.start();
    auto mr = std::make_shared<explorer>(gv);
    vex_context& vctx = s.vctx();
    if (s.status() == Fork) {
        for (auto one_s : tmp_branch) {
            Addr64 oep = one_s->get_oep();
            State* child = one_s->child();

            child->set_trace(mr);

            vctx.pool().enqueue([child, oep, &gv] {

                gk(*child, oep, gv);

                });
        }
    }
   

}


void vmp_reback(State& s) {
    State* state = &s;

    auto bts = s.start();
    GraphView gv;
    auto mr = std::make_shared<explorer>(gv);
    vex_context& vctx = s.vctx();
    if (s.status() == Fork) {
        for (auto one_s : bts) {
            Addr64 oep = one_s->get_oep();
            State* child = one_s->child();

            child->set_trace(mr);

            vctx.pool().enqueue([child, oep, &gv] {

                     gk(*child, oep, gv);
                     
                });
        }
    }
 
};


bool test_creakme() {

    vex_context v(1);
    v.param().set("ntdll_KiUserExceptionDispatcher", (void*)0x777B3BC0);
    v.param().set("Kernel", gen_kernel(Ke::OS_Kernel_Kd::OSK_Windows));
    TR::State state(v, VexArchX86);
    state.read_bin_dump("Y:\\vmp\\Project1.vmp.exe.dump");
    v.hook_read(symbolic_read);

    state.get_trace()->setFlag(CF_traceInvoke);
    //v.hook_read(read);
    //state.setFlag(CF_ppStmts);
    VexGuestAMD64State& amd64_reg_state = state.get_regs_maps()->guest.amd64;
    state.avoid_anti_debugging();

    //005671c8 0f31            rdtsc
   // v.hook_add(0x76F91778, hook2);
    //v.hook_add(0x74c922fc, nullptr, CF_ppStmts);
    
    //state.hook_add(0x756EEFC5, hoo);

    //state.regs.set()

    vmp_reback(state);
    return true;
}
