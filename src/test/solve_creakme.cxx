#include "test.h"
#include <forward_list>
extern "C" {
    #include <ir_opt.h>
}

#include "engine/irsb_cache.h"
#include <spdlog/sinks/basic_file_sink.h>
#include <spdlog/async.h>

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
    return rsval<Long>(s.ctx(), 6);
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

class BlockView {
    irsb_chunk m_ic;
    std::unordered_map<Addr, int> m_nexts;
    std::vector<Addr> m_fork_ea;
public:
    BlockView(irsb_chunk& ic) :m_ic(ic) {
        auto bb = ic->get_irsb();
        if (bb->next->tag == Iex_Const) {
            auto con = bb->next->Iex.Const.con;
            Addr next = con->Ico.U64;
            if (con->tag == Ico_U32) {
                next &= 0xffffffff;
            }
            add_next(next);
        }
    }
    BlockView(irsb_chunk& ic, Addr next) :BlockView(ic) { m_nexts[next] = 0; }
    irsb_chunk get_irsb_chunk() { return m_ic; }
    void add_next(Addr next) {
        m_nexts[next] = 0;
    }
    void ppBlock(TR::vex_context&vctx, std::shared_ptr<spdlog::logger> log) {
        ppIR pp(log, spdlog::level::debug);
        irsb_chunk src = get_irsb_chunk();
        irsb_chunk ic = ado_treebuild( vctx.get_irsb_cache(), src, VexRegUpdSpAtMemAccess);
        auto bb_ea = ic->get_bb_base();
        auto bb_sz = ic->get_bb_size();
        pp.vex_printf("sub_0x%llx : \n\t/*\n\t* checksum:%16llx sz:%x\n\t*/{\n", bb_ea, ic->get_checksum(), bb_sz);
        auto bb = ic->get_irsb();
        int i;
        for (i = 0; i < bb->stmts_used; i++) {
            pp.vex_printf("\t");
            pp.ppIRStmt(bb->stmts[i]);
            pp.vex_printf("\n");
        }
        pp.vex_printf("\tPUT(%d) = ", bb->offsIP);
        pp.ppIRExpr(bb->next);
        pp.vex_printf("; exit-");
        pp.ppIRJumpKind(bb->jumpkind);
        if (m_nexts.size() == 1) {
            //vassert(bb->next->tag == Iex_Const);
            Addr next = m_nexts.begin()->first;
            pp.vex_printf("\n\tjmp sub_0x%llx \n", next);
        }
        else {
            for (auto it = m_nexts.begin(); it != m_nexts.end(); it++) {
                auto next = it->first;
                pp.vex_printf("\n\tif (");
                pp.ppIRExpr(ic->get_irsb()->next);
                pp.vex_printf(")== 0x%x jmp sub_0x%x ;\n", next, next);
            }
            pp.vex_printf("\ttranslate(");
            pp.ppIRExpr(bb->next);
            pp.vex_printf(")");
            pp.vex_printf("}\n");
        }
    }

    void makr_fork_ea(Addr ea){
        auto bb_ea = m_ic->get_bb_base();
        auto bb_sz = m_ic->get_bb_size();
        vassert(bb_ea <= ea && bb_ea + bb_sz >= ea);
        m_fork_ea.emplace_back(ea);
    }

    bool check_fork_ea(Addr ea) {
        return std::find(m_fork_ea.begin(), m_fork_ea.end(), ea) != m_fork_ea.end();
    }
};
class GraphView {
    using _jmps = std::forward_list<Addr>;
    template<typename Addr> friend class PathExplorer;

    spin_mutex translate_mutex;
    TR::vex_context& m_vctx;
    using BBKey = std::pair <Addr, size_t>;

    class BBKeyHash
    {
    public:
        size_t operator()(const BBKey& name) const
        {
            return std::hash<size_t>()(name.first ^ name.second);
        }
    };

    std::unordered_map<BBKey, BlockView, BBKeyHash> m_blocks;
    

public:
    std::shared_ptr<spdlog::logger> log;
    GraphView(TR::vex_context& vctx) :m_vctx(vctx) {
        log = spdlog::basic_logger_mt<spdlog::async_factory>("ircode", "ircode.txt");
        log->set_level(spdlog::level::debug);
        log->set_pattern("%v");
    }

    ~GraphView() {
        ppGraphView();
    }
    void ppGraphView() {
        auto it = m_blocks.begin();
        for (; it != m_blocks.end(); it++) {
            auto sub_ep = it->first.first;
            auto check_sum = it->first.second;
            BlockView& basic_irsb_chunk = it->second;
            vassert(check_sum == basic_irsb_chunk.get_irsb_chunk()->get_checksum());
            vassert(sub_ep == basic_irsb_chunk.get_irsb_chunk()->get_bb_base());
            basic_irsb_chunk.ppBlock(m_vctx, log);
        }
    }
    void add_block(irsb_chunk irsb_chunk, Addr next);
    void add_exit(irsb_chunk irsb_chunk, Addr code_ea, Addr next);
    void state_task(State& s);
    void explore_block(State* s);

    auto mk_irsb_chunk_key(irsb_chunk irsb_chunk) {
        auto ea = irsb_chunk->get_bb_base();
        auto checksum = irsb_chunk->get_checksum();
        return BBKey(std::make_pair(ea, checksum));
    }
    void mark_is_fork_ea(irsb_chunk irsb_chunk, Addr code_ea) {
        auto key = mk_irsb_chunk_key(irsb_chunk);
        auto it = m_blocks.find(key);
        if (it == m_blocks.end()) {
            vassert(0);
            m_blocks.emplace(key, BlockView(irsb_chunk));
        }
        else {
            it->second.makr_fork_ea(code_ea);
        }

    }

    bool check_is_fork_ea(irsb_chunk irsb_chunk, Addr code_ea) {
        auto key = mk_irsb_chunk_key(irsb_chunk);
        auto it = m_blocks.find(key);

        if (it == m_blocks.end()) {
            vassert(0);
            m_blocks.emplace(key, BlockView(irsb_chunk));
            return false;
        }
        else {
            return it->second.check_fork_ea(code_ea);
        }
    }

    bool is_block_exist(irsb_chunk irsb_chunk) {
        auto key = mk_irsb_chunk_key(irsb_chunk);
        auto it = m_blocks.find(key);
        return it != m_blocks.end();
    }

};


class explorer : public TraceInterface {
    GraphView& m_gv;
    UInt m_IMark_stmtn;
public:
    explorer(GraphView& gv) :m_gv(gv) {
    }
    
    virtual void traceStart(State& s, HWord ea);
        virtual void traceIRSB(State& s, HWord ea, irsb_chunk&);;
            virtual void traceIRStmtStart(State& s, irsb_chunk&, UInt stmtn);
            virtual void traceIRStmtEnd(State& s, irsb_chunk& irsb, UInt stmtn);
        virtual void traceIRnext(State& s, irsb_chunk& irsb, const tval& next);
        virtual void traceIrsbEnd(State& s, irsb_chunk&);
    virtual void traceFinish(State& s, HWord ea);

    virtual  std::shared_ptr<TraceInterface> mk_new_TraceInterface() override { return std::make_shared<explorer>(m_gv); }
    virtual ~explorer() {}
};


void explorer::traceStart(State& s, HWord ea)
{
    TraceInterface::traceStart(s, ea);
}

void explorer::traceIRSB(State& s, HWord ea, irsb_chunk& irsb)
{
    TraceInterface::traceIRSB(s, ea, irsb);

   // AstBlock ab(irsb);
   //ppIRSB(irsb->get_irsb());
}
extern
bool false_exit_check(Addr& guard_false_entry, UInt IMark_stmtn, UInt exit_stmtn, const IRSB* irsb);


void explorer::traceIRStmtStart(State& s, irsb_chunk& bb, UInt stmtn)
{
    TraceInterface::traceIRStmtStart(s, bb, stmtn);
    IRSB* irsb = bb->get_irsb();

    //ppIR pp(m_gv.log);
    IRStmt* st = irsb->stmts[stmtn];
    if (st->tag == Ist_IMark) {
        m_IMark_stmtn = stmtn;
    }
    if (st->tag == Ist_Exit) {
        Addr64 exitptr = st->Ist.Exit.dst->Ico.U64;
        if (st->Ist.Exit.dst->tag == Ico_U32) exitptr &= 0xffffffff;
        m_gv.add_exit(bb, s.get_cpu_ip(), exitptr);
        rsbool guard = s.tIRExpr(st->Ist.Exit.guard).tobool();
        if LIKELY(guard.real()) {
            if LIKELY(guard.tor()) {
            }
        }
        else {
            m_gv.mark_is_fork_ea(bb, s.get_cpu_ip());
        }
    }
    //    
    //    Addr64 exitptr = st->Ist.Exit.dst->Ico.U64;
    //    if (st->Ist.Exit.dst->tag == Ico_U32) exitptr &= 0xffffffff;

    //    Addr guard_false_entry;

    //    if (false_exit_check(guard_false_entry, m_IMark_stmtn, stmtn, irsb)) {

    //    }

    //    if LIKELY(guard.real()) {
    //        if LIKELY(guard.tor()) {
    //        }
    //    }
    //    else {
    //        pp.vex_printf("if (");
    //        pp.ppIRExpr(st->Ist.Exit.guard);
    //        pp.vex_printf("){\n");

    //        pp.vex_printf("\tjmp sub_0x%x", exitptr);

    //        pp.vex_printf("\n}\n");

    //    }

    //    /*UInt tmp = st->Ist.WrTmp.tmp;
    //    pp.vex_printf("t%u = ", tmp, s.irvex()[tmp].str().c_str());
    //    pp.ppIRExpr(st->Ist.WrTmp.data);
    //    pp.vex_printf("\t%s", s.irvex()[tmp].str().c_str());*/
    //}
    //else {
    //    pp.ppIRStmt(st);
    //}
}

void explorer::traceIRStmtEnd(State& s, irsb_chunk& irsb, UInt stmtn)
{
    TraceInterface::traceIRStmtEnd(s, irsb, stmtn);

}

void explorer::traceIRnext(State& s, irsb_chunk& irsb, const tval& next)
{
    TraceInterface::traceIRnext(s, irsb, next);

    //ppIR pp(m_gv.log);

    std::deque<sv::tval> result;
    if (next.real()) {
        Addr64 ptr = next;
        if (next.nbits() == 32)  ptr &= 0xffffffff;
        m_gv.add_block(irsb, ptr);
    }
    else {
        Int eval_size = eval_all(result, s.solv, next);
        if (eval_size <= 0) {
            throw Expt::SolverNoSolution("eval_size <= 0", s.solv);
        }
        else {
            for (auto re : result) {
                Addr64 ptr = re;
                if (re.nbits() == 32)  ptr &= 0xffffffff;
                m_gv.add_block(irsb, ptr);
            }
        }
    }
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
        vkd = s.emu_irsb<32>(tmp_branch, guest_start, m_status, irsb);
    }
    else {
        vkd = s.emu_irsb<64>(tmp_branch, guest_start, m_status, irsb);
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
    vex_context& vctx = s.vctx();


    //if (s.status() == Fork) {
    //    for (auto one_s : tmp_branch) {
    //        Addr64 oep = one_s->get_oep();
    //        State* child = one_s->child();

    //        child->set_trace(std::make_shared<explorer>(gv));

    //        vctx.pool().enqueue([child, oep, &gv] {

    //            gk(*child, oep, gv);

    //            });
    //    }
    //}
   

}

void GraphView::add_block(irsb_chunk irsb_chunk, Addr next)
{
    auto ea = irsb_chunk->get_bb_base();
    auto checksum = irsb_chunk->get_checksum();
    auto key = BBKey(std::make_pair(ea, checksum));
    auto it = m_blocks.find(key);
    if (it == m_blocks.end()) {
        m_blocks.emplace(key, BlockView(irsb_chunk, next));
    }
    else{
        it->second.add_next(next);
    }
}

void GraphView::add_exit(irsb_chunk irsb_chunk, Addr code_ea, Addr next)
{
    auto ea = irsb_chunk->get_bb_base();
    auto checksum = irsb_chunk->get_checksum();
    auto key = BBKey(std::make_pair(ea, checksum));
    auto it = m_blocks.find(key);
    if (it == m_blocks.end()) {
        m_blocks.emplace(key, BlockView(irsb_chunk));
    }
}

void GraphView::state_task(State& s) {

    //s.get_trace()->setFlags(CF_traceJmp);
    //s.get_trace()->setFlags(CF_ppStmts);
    //s.vctx().hook_add(0x551AF328, nullptr, CF_ppStmts);
    Vex_Kind vkd;
    vex_context& vctx = s.vctx();
    std::deque<TR::State::BtsRefType> tmp_branch = s.start();

}

void GraphView::explore_block(State* s)
{
    s->set_trace(std::make_shared<explorer>(*this));
    auto bts = s->start();


    vex_context& vctx = s->vctx();
    //vctx.param().set()
    Addr fork_ea = s->get_cpu_ip();
    //auto fork_bb = s.get_last_bb();



    if (s->status() == Fork) {
        for (auto one_s : bts) {
            Addr64 oep = one_s->get_oep();

            State* child = one_s->child();
            //child->set_trace(std::make_shared<explorer>(*this));
            child->set_irvex(std::make_shared< EmuEnvGuest>(child->vctx(), child->vinfo(), child->mem));
            auto fork_bb = child->irvex().translate_front(oep);
            if (is_block_exist(fork_bb)) {
                spdlog::info("fork_ea:{:x} is fork. ep: {:x}", fork_ea, 0);
                child->set_irvex(nullptr);
                
            }
            else {
                vctx.pool().enqueue([this, child] {
                    explore_block(child);
                    });
            }


        }
    }
}


void vmp_reback(State& s) {
    GraphView gv(s.vctx());
    gv.explore_block(&s);
    s.vctx().pool().wait();
    spdlog::info("state:{}", (std::string)s);
};


bool test_creakme() {
    vex_context v(4);
    v.param().set("ntdll_KiUserExceptionDispatcher", std::make_shared<TR::sys_params_value>((size_t)0x777B3BC0));
    v.param().set("Kernel", gen_kernel(Ke::OS_Kernel_Kd::OSK_Windows));
    TR::State state(v, VexArchX86);
    state.read_bin_dump("Y:\\vmp\\Project1.vmp.exe.dump");
    

    state.get_trace()->setFlag(CF_traceInvoke);
    //v.hook_read(read);
    v.hook_read(symbolic_read);
    state.get_trace()->setFlag(CF_ppStmts);
    VexGuestAMD64State& amd64_reg_state = state.get_regs_maps()->guest.amd64;
    state.avoid_anti_debugging();
    state.set_level(spdlog::level::debug);
    //auto bts = state.start();
    //005671c8 0f31            rdtsc
   // v.hook_add(0x76F91778, hook2);
    //v.hook_add(0x74c922fc, nullptr, CF_ppStmts);
    
    //v.hook_add(0x50dd56a7, hoo);

    //state.regs.set()

    vmp_reback(state);
    return true;
}
