
#include <llvm/Support/GraphWriter.h>
#include <llvm/Support/DOTGraphTraits.h>
#include <vexllvm/genllvm.h>
#include <vexllvm/vexhelpers.h>
#include <vexllvm/vexsb.h>

#include "instopt/engine/tr_ir_opt.h"
#include "instopt/engine/state_explorer.h"
#include <forward_list>
#include <spdlog/async.h>
#include <spdlog/sinks/basic_file_sink.h>
extern "C" {
#include <src/valgrind-3.17.0/VEX/priv/ir_opt.h>
};

// ===============================================================================================================================
#include <set>
#include <vector>
#include "instopt/engine/irsb_cache.h"

using namespace TR;

#define DEBUG 1


class BlockView {
    irsb_chunk m_ic;
    std::set< BlockView* > m_nexts;
    std::vector<Addr> m_fork_ea;
    BlockView(irsb_chunk& ic) :m_ic(ic) {}
public:
    class BlockViewKeyHash
    {
    public:
        size_t operator()(const BlockView*& name) const
        {
            return std::hash<size_t>()(name->m_ic->get_bb_base() ^ name->m_ic->get_checksum());
        }
    };
public:
    BlockView(irsb_chunk& ic, BlockView* next) :m_ic(ic) { add_next(next); }
    BlockView(const BlockView& B) :m_ic(B.m_ic), m_nexts(B.m_nexts), m_fork_ea(B.m_fork_ea) {}
    void operator =(const BlockView& B) {
        this->~BlockView();
        new (this) BlockView(B);
    }
    ~BlockView(){}
    static BlockView mk_root(irsb_chunk& ic) { return BlockView(ic); }
    irsb_chunk get_irsb_chunk() const { return m_ic; }
    void add_next(BlockView* next) {
        if (next) {
            m_nexts.emplace(next);
        }
    }
    inline const  std::set< BlockView* >& get_nexts() const { return m_nexts; }

    void ppBlock(TR::vex_context& vctx, std::shared_ptr<spdlog::logger> log, bool treebuild = false);



    void makr_fork_ea(Addr ea) {
        auto bb_ea = m_ic->get_bb_base();
        auto bb_sz = m_ic->get_bb_size();
        vassert(bb_ea <= ea && bb_ea + bb_sz >= ea);
        m_fork_ea.emplace_back(ea);
    }

    bool check_fork_ea(Addr ea) {
        return std::find(m_fork_ea.begin(), m_fork_ea.end(), ea) != m_fork_ea.end();
    }

};

inline void BlockView::ppBlock(TR::vex_context& vctx, std::shared_ptr<spdlog::logger> log, bool treebuild) {
    ppIR pp(log, spdlog::level::debug);
    irsb_chunk src = get_irsb_chunk();
    irsb_chunk ic = src;
    if (treebuild) {
        ic = ado_treebuild(vctx.get_irsb_cache(), src, VexRegUpdSpAtMemAccess);
    }
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
        auto next = *m_nexts.begin();
        Addr next_ea = next->get_irsb_chunk()->get_bb_base();
        pp.vex_printf("\n\tjmp sub_0x%llx \n", next_ea);
    }
    else {
        for (std::set< BlockView* >::iterator it = m_nexts.begin(); it != m_nexts.end(); ++it) {
            Addr next = (*it)->get_irsb_chunk()->get_bb_base();
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



// ===============================================================================================================================



class GraphView {
    using _jmps = std::forward_list<Addr>;
    template<typename Addr> friend class PathExplorer;

    // spin_mutex translate_mutex;
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
public:
    using BlocksTy = typename std::unordered_map<BBKey, BlockView, BBKeyHash>;
    using MutiBlocksTy = typename std::unordered_map<Addr, std::shared_ptr<std::vector<BlockView>>>;
private:
    BlocksTy m_blocks;
    MutiBlocksTy m_mutiBlocks;

public:
    class ExplodedGraph {
    public:
        GraphView& graph_view;

        using nodes_iterator = GraphView::BlocksTy::iterator;
        using NodeRef = const BlockView*;

        //std::vector<NodeRef> node;
        std::vector<NodeRef> nodes;
        ExplodedGraph(GraphView& GV) :graph_view(GV) {
            auto& blocks = graph_view.get_blocks();
            nodes.reserve(blocks.size());
            auto it = blocks.begin();
            for (; it != blocks.end(); it++) {
                auto sub_ep = it->first.first;
                auto check_sum = it->first.second;
                const BlockView& basic_irsb_chunk = it->second;
                //basic_irsb_chunk.ppBlock(m_vctx, log);
                nodes.emplace_back(&basic_irsb_chunk);
            }
        }

    };

    std::shared_ptr<spdlog::logger> log;
    GraphView(TR::vex_context& vctx);

    ~GraphView() {  }

    std::shared_ptr<TraceInterface> mk_explore();

    const BlocksTy& get_blocks() { return m_blocks; };
    const MutiBlocksTy& get_MutiBlocks() { return m_mutiBlocks; };

    void ppGraphView(bool treebuild = false);

    std::string creat_graph(const char* dotName = "CFG");
    void simplify();
    llvm::Function* emitOneBlock(BlockView BV);


    BlockView* add_block(irsb_chunk irsb_chunk, BlockView* next);
    BlockView* add_block(BBKey& bk, BlockView bv);


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
            //m_blocks.emplace(key, BlockView(irsb_chunk));
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
            //m_blocks.emplace(key, BlockView(irsb_chunk));
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



static unsigned arch_word_size_bits(VexArch arch) {
    switch (arch) {
    case VexArchX86:
    case VexArchARM:
    case VexArchMIPS32:
    case VexArchNANOMIPS:
    case VexArchPPC32:
        return 32;

    case VexArchAMD64:
    case VexArchARM64:
    case VexArchMIPS64:
    case VexArchPPC64:
    case VexArchS390X:
        return 64;

    default:
        vassert(0);
    }
}

#include "genllvm.h"
#include "Sugar.h"
#include "vexsb.h"
#include "vexstmt.h"
#include "vexexpr.h"
#include "vexcpustate.h"
using namespace llvm;

class TRVexStmtExit : public VexStmtExit
{
    GraphView& GV;
    std::unique_ptr<GenLLVM>& theGenLLVM = GenLLVM::getGenLLVM();
public:
    TRVexStmtExit(GraphView& GV, VexSB* in_parent, const IRStmt* in_stmt) :VexStmtExit(in_parent, in_stmt), GV(GV) {};
    virtual ~TRVexStmtExit() {};
    virtual void emit(void) const;;
};
class RBVexSB : public VexSB {
    GraphView& GV;
    std::unique_ptr<GenLLVM>& theGenLLVM = GenLLVM::getGenLLVM();

public:
    RBVexSB(GraphView& GV, guest_ptr guess_addr, const IRSB* in_irsb) :VexSB(guess_addr, in_irsb->tyenv->types_used, in_irsb->tyenv->types), GV(GV) {
        stmt_c = in_irsb->stmts_used;
        loadInstructions(in_irsb);
        loadJump(in_irsb->jumpkind, VexExpr::create(stmts.back().get(), in_irsb->next));
    }
    void loadInstructions(const IRSB* irsb)
    {
        // ppIRSB(const_cast<IRSB*>(irsb));
        for (unsigned int i = 0; i < getNumStmts(); i++) {
            VexStmt* stmt;
            VexStmtIMark* imark;

            stmt = loadNextInstruction(irsb->stmts[i]);
            stmts.push_back(std::unique_ptr<VexStmt>(stmt));

            imark = dynamic_cast<VexStmtIMark*>(stmt);
            if (imark != NULL) last_imark = imark;
        }
    }

    VexStmt* loadNextInstruction(const IRStmt* stmt)
    {
        VexStmt* vs;
#define TAGOP(x) case Ist_##x : vs = new VexStmt##x(this, stmt); break;

        switch (stmt->tag) {
            TAGOP(NoOp);
            TAGOP(IMark);
            TAGOP(AbiHint);
            TAGOP(Put);
            TAGOP(PutI);
            TAGOP(WrTmp);
            TAGOP(Store);
            TAGOP(CAS);
            TAGOP(LLSC);
            TAGOP(Dirty);
            TAGOP(MBE);
            TAGOP(StoreG);
            TAGOP(LoadG);
        case Ist_Exit: vs = new TRVexStmtExit(GV, this, stmt); break;
        default:
            fprintf(stderr, "??? tag=%x\n", stmt->tag);
            assert(0 && "SIMPLE HUMAN");
            break;
        }
        return vs;
    }

    virtual void emit_one() {

        llvm::Value* ret_v;

        memset(values, 0, sizeof(Value*) * getNumRegs());


        for (auto& stmt : stmts)
            stmt->emit();

        /* compute goto */
        ret_v = jump_expr->emit();


        /* record exit type */
        switch (jump_kind) {
        case Ijk_Boring:
        case Ijk_NoRedir:
        case Ijk_ClientReq:
            /* nothing, boring */
            break;
        case Ijk_Call:
            theGenLLVM->setExitType(GE_CALL);
            break;
        case Ijk_Ret:
            theGenLLVM->setExitType(GE_RETURN);
            break;
        case Ijk_Yield:
            theGenLLVM->setExitType(GE_YIELD);
            break;

        case Ijk_Sys_sysenter:
        case Ijk_Sys_syscall:
            theGenLLVM->setExitType(GE_SYSCALL);
            break;
        case Ijk_Sys_int128:
            theGenLLVM->setExitType(GE_INT);
            break;
        case Ijk_SigTRAP:
            theGenLLVM->setExitType(GE_SIGTRAP);
            break;
        default:
            fprintf(stderr, "UNKNOWN JUMP TYPE %x\n", jump_kind);
            //assert(0 == 1 && "BAD JUMP");
        }

        if (const VexExprConst* Con = dynamic_cast<const VexExprConst*>(jump_expr)) {
            guest_ptr dst(Con->toValue());
            if (dst == guest_addr) {
                IRBuilder<>* builder;
                builder = theGenLLVM->getBuilder();
                builder->CreateRet(ret_v);
            }
            else {
                auto MB = GV.get_MutiBlocks();
                if (MB.find(dst) != MB.end()) {
                    for (auto B : *MB[dst].get()) {
                        guest_ptr guest_addr;
                        ppIRSB(B.get_irsb_chunk()->get_irsb());
                        RBVexSB vsb(GV, guest_addr, B.get_irsb_chunk()->get_irsb());
                        vsb.emit_one();
                    }
                }
            }
        }
        else {
            IRBuilder<>* builder;

            builder = theGenLLVM->getBuilder();
            builder->CreateRet(ret_v);
            /* return goto */
            //cur_f = theGenLLVM->endBB(ret_v);
        }


    }

    virtual llvm::Function* emit(const char* fname = "vexsb_f") override {

        llvm::Function* cur_f;
        llvm::Value* ret_v;

        theGenLLVM->beginBB(fname);

        memset(values, 0, sizeof(Value*) * getNumRegs());

        for (auto& stmt : stmts)
            stmt->emit();

        /* compute goto */
        ret_v = jump_expr->emit();


        /* record exit type */
        switch (jump_kind) {
        case Ijk_Boring:
        case Ijk_NoRedir:
        case Ijk_ClientReq:
            /* nothing, boring */
            break;
        case Ijk_Call:
            theGenLLVM->setExitType(GE_CALL);
            break;
        case Ijk_Ret:
            theGenLLVM->setExitType(GE_RETURN);
            break;
        case Ijk_Yield:
            theGenLLVM->setExitType(GE_YIELD);
            break;

        case Ijk_Sys_sysenter:
        case Ijk_Sys_syscall:
            theGenLLVM->setExitType(GE_SYSCALL);
            break;
        case Ijk_Sys_int128:
            theGenLLVM->setExitType(GE_INT);
            break;
        case Ijk_SigTRAP:
            theGenLLVM->setExitType(GE_SIGTRAP);
            break;
        default:
            fprintf(stderr, "UNKNOWN JUMP TYPE %x\n", jump_kind);
            //assert(0 == 1 && "BAD JUMP");
        }

        if (const VexExprConst* Con = dynamic_cast<const VexExprConst*>(jump_expr)) {
            guest_ptr dst(Con->toValue());
            if (dst == guest_addr) {
                IRBuilder<>* builder;
                builder = theGenLLVM->getBuilder();
                builder->CreateRet(ret_v);
            }
            else {
                auto MB = GV.get_MutiBlocks();
                if (MB.find(dst) != MB.end()) {
                    for (auto B : *MB[dst].get()) {
                        guest_ptr guest_addr;
                        ppIRSB(B.get_irsb_chunk()->get_irsb());
                        RBVexSB vsb(GV, guest_addr, B.get_irsb_chunk()->get_irsb());
                        vsb.emit_one();
                    }
                }
            }
        }
        else {
            IRBuilder<>* builder;

            builder = theGenLLVM->getBuilder();
            builder->CreateRet(ret_v);
            /* return goto */
        }


        //cur_f = theGenLLVM->endBB(ret_v);
        return cur_f;



    }
};



void GraphView::simplify() {
    std::deque<std::pair<int, BlockView>> chain;
    UInt ea = 0x44b26c;
    size_t checksum = 0x6bf1af95973564c5;

    //IRSB* dst = emptyIRSB();

    //for (;;) {
    //    auto key = BBKey(std::make_pair(ea, checksum));
    //    auto it = m_blocks.find(key);
    //    if (it == m_blocks.end())
    //        break;

    //    BlockView& BLK = it->second;

    //    // concatenate_irsbs(dst, BLK.get_irsb_chunk()->get_irsb());
    //    guest_ptr guest_addr;
    //    unsigned int num_regs;
    //    IRType* in_types;



    //}


    Guest& gs = (Guest&)(*(Guest*)(nullptr));
    //theGenLLVM =
    GenLLVM::getGenLLVM() = std::make_unique<GenLLVM>(gs);
    VexHelpers::getVexHelpers() = VexHelpers::create(VexArchX86);
#if 1

    auto blocks = get_MutiBlocks();
    auto E = blocks.find(0x47f82f)->second;
    
    
    BlockView& basic_irsb_chunk = E.get()->operator[](0);
    ppIRSB(basic_irsb_chunk.get_irsb_chunk()->get_irsb());

    VexArch arch = basic_irsb_chunk.get_irsb_chunk()->get_arch();
    VexHelpers::getVexHelpers()->loadDefaultModules(arch);
    GenLLVM::getGenLLVM()->mkFuncTy(arch_word_size_bits(arch));
    guest_ptr guest_addr;
    RBVexSB vsb(*this, guest_addr, basic_irsb_chunk.get_irsb_chunk()->get_irsb());
    std::stringstream st;
    st << "bb_" << std::hex << basic_irsb_chunk.get_irsb_chunk()->get_bb_base() << "_" << std::dec << basic_irsb_chunk.get_irsb_chunk()->get_bb_base();
    vsb.emit(st.str().c_str());
    // break;
    // break;
    
#else

    auto it = m_blocks.begin();
    for (; it != m_blocks.end(); it++) {
        auto sub_ep = it->first.first;
        auto check_sum = it->first.second;
        BlockView& basic_irsb_chunk = it->second;

        irsb_chunk irsb = basic_irsb_chunk.get_irsb_chunk();
#if 0
        if (irsb->get_bb_base() != 0x49a45c) {
            continue;
        }
        ppIRSB(basic_irsb_chunk.get_irsb_chunk()->get_irsb());
#endif
        VexArch arch = irsb->get_arch();
        VexHelpers::getVexHelpers()->loadDefaultModules(arch);
        GenLLVM::getGenLLVM()->mkFuncTy(arch_word_size_bits(arch));
        guest_ptr guest_addr;
        VexSB vsb(guest_addr, irsb->get_irsb());
        std::stringstream st;
        st << "bb_" << std::hex << irsb->get_bb_base() << "_" << std::dec << irsb->get_bb_base();
        
        vsb.emit(st.str().c_str());
        //break;
        // break;
    }
#endif
    // GenLLVM::getGenLLVM()->getBuilder()
    StoreModuleIRToFile(&GenLLVM::getGenLLVM()->getModule(), "vmp.ll", false);
    // clang -emit-llvm -S vmp.bc -o vmp.ll
    StoreModuleToFile(&GenLLVM::getGenLLVM()->getModule(), "vmp.bc", false);
    // llc.exe -filetype=obj -O3 ./vmp.bc -o vmp3.o

    


}

llvm::Function* GraphView::emitOneBlock(BlockView BV)
{
    guest_ptr guest_addr;
    RBVexSB vsb(*this, guest_addr, BV.get_irsb_chunk()->get_irsb());
    return vsb.emit();
}

inline GraphView::GraphView(TR::vex_context& vctx) :m_vctx(vctx), m_mutiBlocks(){
    log = spdlog::basic_logger_mt<spdlog::async_factory>("ircode", "ircode.txt");
    log->set_level(spdlog::level::debug);
    log->set_pattern("%v");
}






inline void GraphView::ppGraphView(bool treebuild) {
    auto it = m_blocks.begin();
    for (; it != m_blocks.end(); it++) {
        auto sub_ep = it->first.first;
        auto check_sum = it->first.second;
        BlockView& basic_irsb_chunk = it->second;
        vassert(check_sum == basic_irsb_chunk.get_irsb_chunk()->get_checksum());
        vassert(sub_ep == basic_irsb_chunk.get_irsb_chunk()->get_bb_base());
        basic_irsb_chunk.ppBlock(m_vctx, log, treebuild);
    }
}


BlockView* GraphView::add_block(irsb_chunk bck_irsb, BlockView* next)
{
    auto ea = bck_irsb->get_bb_base();
    auto checksum = bck_irsb->get_checksum();
    auto key = BBKey(std::make_pair(ea, checksum));
    auto it = m_blocks.find(key);
    if (it == m_blocks.end()) {
        return add_block(key, BlockView(bck_irsb, next));
    }
    else {
        it->second.add_next(next);
        return &it->second;
    }
}

BlockView* GraphView::add_block(BBKey& bk, BlockView bv)
{
    auto F = m_mutiBlocks.find(bk.first);
    if (F == m_mutiBlocks.end()) {
        std::vector<BlockView> v ;
        v.push_back(bv);
        m_mutiBlocks.emplace(bk.first, std::make_shared<std::vector<BlockView>>(std::move(v)));
    }
    else {
        assert(F->second.get());
        F->second->push_back(bv);
    }
    m_mutiBlocks.emplace();
    return &m_blocks.emplace(bk, bv).first->second;

}


void GraphView::add_exit(irsb_chunk irsb_chunk, Addr code_ea, Addr next)
{
    auto ea = irsb_chunk->get_bb_base();
    auto checksum = irsb_chunk->get_checksum();
    auto key = BBKey(std::make_pair(ea, checksum));
    auto it = m_blocks.find(key);
    if (it == m_blocks.end()) {
        //m_blocks.emplace(key, BlockView(irsb_chunk));
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
    s->set_trace(mk_explore());
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


// ===============================================================================================================================


class explorer : public TraceInterface {
    GraphView& m_gv;
    UInt m_IMark_stmtn;
    irsb_chunk bck_irsb;
public:
    explorer(GraphView& gv) :m_gv(gv) {
    }
    void update_block_chain(irsb_chunk curr) {
        if (bck_irsb) {
            m_gv.add_block(bck_irsb, m_gv.add_block(curr, nullptr));
        }
        else {
            m_gv.add_block(curr, nullptr);
        }
        bck_irsb = curr;
    }
    virtual void traceStart(State& s, HWord ea) override;
    virtual void traceIRSB(State& s, HWord ea, irsb_chunk&) override;
    virtual void traceIRStmtStart(State& s, irsb_chunk&, UInt stmtn) override;
    virtual void traceIRStmtEnd(State& s, irsb_chunk& irsb, UInt stmtn) override;
    virtual void traceIRnext(State& s, irsb_chunk& irsb, const tval& next) override;
    virtual void traceIrsbEnd(State& s, irsb_chunk&) override;
    virtual void traceFinish(State& s, HWord ea) override;

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
    // ppIRSB(irsb->get_irsb());
    if (DEBUG) {
        s.logger->info("{:x} {:x}", irsb->get_bb_base(), s.get_cpu_sp());
    }
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
        //m_gv.add_exit(bb, s.get_cpu_ip(), exitptr);
        //update_block_chain(bb);
        rsbool guard = s.tIRExpr(st->Ist.Exit.guard).tobool();
        if LIKELY(guard.real()) {
            if LIKELY(guard.tor()) {
                update_block_chain(bb);
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
    update_block_chain(irsb);
    //ppIR pp(m_gv.log);



    //std::deque<sv::tval> result;
    //if (next.real()) {
    //    Addr64 ptr = next;
    //    if (next.nbits() == 32)  ptr &= 0xffffffff;
    //    //m_gv.add_block(bck_irsb, ptr);
    //}
    //else {
    //    Int eval_size = eval_all(result, s.solv, next);
    //    if (eval_size <= 0) {
    //        throw Expt::SolverNoSolution("eval_size <= 0", s.solv);
    //    }
    //    else {
    //        for (auto re : result) {
    //            Addr64 ptr = re;
    //            if (re.nbits() == 32)  ptr &= 0xffffffff;
    //            //m_gv.add_block(bck_irsb, ptr);
    //        }
    //    }
    //}
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




// ===============================================================================================================================


namespace llvm {
    template <>
    struct DOTGraphTraits<GraphView::ExplodedGraph*> : public DefaultDOTGraphTraits {
        DOTGraphTraits(bool simple = false) : DefaultDOTGraphTraits(simple) {}



    private:
        bool IsSimple;

    protected:
        bool isSimple() {
            return IsSimple;
        }

    public:
        /// getGraphName - Return the label for the graph as a whole.  Printed at the 
        /// top of the graph. 
        /// 
        template<typename GraphType>
        static std::string getGraphName(const GraphType& G) { return ""; }

        /// getGraphProperties - Return any custom properties that should be included 
        /// in the top level graph structure for dot. 
        /// 
        template<typename GraphType>
        static std::string getGraphProperties(const GraphType&) {
            //return "graph [rankdir=LR];";
            return "";
        }

        /// renderGraphFromBottomUp - If this function returns true, the graph is 
        /// emitted bottom-up instead of top-down.  This requires graphviz 2.0 to work 
        /// though. 
        static bool renderGraphFromBottomUp() {
            return false;
        }

        /// isNodeHidden - If the function returns true, the given node is not 
        /// displayed in the graph. 
        template<typename GraphType>
        static bool isNodeHidden(const void*, const GraphType&) {
            return false;
        }

        /// getNodeLabel - Given a node and a pointer to the top level graph, return 
        /// the label to print in the node. 
        template<typename GraphType>
        std::string getNodeLabel(const void* n, const GraphType& G) {
            const BlockView* node = static_cast<const BlockView*>(n);
            std::stringstream st;
            irsb_chunk irsb = node->get_irsb_chunk();
            st << " ea:" << std::hex << irsb->get_bb_base() << std::hex << " sz:" << irsb->get_bb_size() << "\n" << irsb->get_checksum();
            return st.str();
        }

        // getNodeIdentifierLabel - Returns a string representing the 
        // address or other unique identifier of the node. (Only used if 
        // non-empty.) 
        template <typename GraphType>
        static std::string getNodeIdentifierLabel(const void* n, const GraphType& G) {
            const BlockView* node = static_cast<const BlockView*>(n);
            std::shared_ptr<spdlog::logger> log;
            // ppIR pp(log, spdlog::level::off);
            // irsb_chunk ic = node->get_irsb_chunk();
            // auto bb_ea = ic->get_bb_base();
            // auto bb_sz = ic->get_bb_size();
            //// pp.vex_printf("sub_0x%llx : \n\t/*\n\t* checksum:%16llx sz:%x\n\t*/{\n", bb_ea, ic->get_checksum(), bb_sz);
            // auto bb = ic->get_irsb();
            // int i;
            // for (i = 0; i < bb->stmts_used; i++) {
            //     pp.vex_printf("\t");
            //     pp.ppIRStmt(bb->stmts[i]);
            //     pp.vex_printf("\n");
            // }
            // pp.vex_printf("\tPUT(%d) = ", bb->offsIP);
            // pp.ppIRExpr(bb->next);
            // return pp.str();
            return "";
        }

        template<typename GraphType>
        static std::string getNodeDescription(const void*, const GraphType&) {
            return "";
        }

        /// If you want to specify custom node attributes, this is the place to do so 
        /// 
        template<typename GraphType>
        static std::string getNodeAttributes(const void*, const GraphType&) {
            return "";
        }

        /// If you want to override the dot attributes printed for a particular edge, 
        /// override this method. 
        template<typename EdgeIter, typename GraphType>
        static std::string getEdgeAttributes(const void*, EdgeIter,
            const GraphType&) {
            return "";
        }

        /// getEdgeSourceLabel - If you want to label the edge source itself, 
        /// implement this method. 
        template<typename EdgeIter>
        static std::string getEdgeSourceLabel(const void*, EdgeIter) {
            return "";
        }

        /// edgeTargetsEdgeSource - This method returns true if this outgoing edge 
        /// should actually target another edge source, not a node.  If this method is 
        /// implemented, getEdgeTarget should be implemented. 
        template<typename EdgeIter>
        static bool edgeTargetsEdgeSource(const void*, EdgeIter) {
            return false;
        }

        /// getEdgeTarget - If edgeTargetsEdgeSource returns true, this method is 
        /// called to determine which outgoing edge of Node is the target of this 
        /// edge. 
        template<typename EdgeIter>
        static EdgeIter getEdgeTarget(const void*, EdgeIter I) {
            return I;
        }

        /// hasEdgeDestLabels - If this function returns true, the graph is able 
        /// to provide labels for edge destinations. 
        static bool hasEdgeDestLabels() {
            return false;
        }

        /// numEdgeDestLabels - If hasEdgeDestLabels, this function returns the 
        /// number of incoming edge labels the given node has. 
        static unsigned numEdgeDestLabels(const void*) {
            return 0;
        }

        /// getEdgeDestLabel - If hasEdgeDestLabels, this function returns the 
        /// incoming edge label with the given index in the given node. 
        static std::string getEdgeDestLabel(const void*, unsigned) {
            return "";
        }

        /// addCustomGraphFeatures - If a graph is made up of more than just 
        /// straight-forward nodes and edges, this is the place to put all of the 
        /// custom stuff necessary.  The GraphWriter object, instantiated with your 
        /// GraphType is passed in as an argument.  You may call arbitrary methods on 
        /// it to add things to the output graph. 
        /// 
        template<typename GraphType, typename GraphWriter>
        static void addCustomGraphFeatures(const GraphType&, GraphWriter&) {}
    };






    template<>
    struct GraphTraits<GraphView::ExplodedGraph*> {
    public:
        using GraphTy = GraphView::ExplodedGraph*;


        using NodeRef = const BlockView*;
        using nodes_iterator = std::vector<NodeRef>::iterator;

        using ChildIteratorType = std::set< BlockView*, BlockView::BlockViewKeyHash >::iterator;

        static nodes_iterator nodes_begin(GraphTy n) {
            return n->nodes.begin();
        }

        static nodes_iterator nodes_end(GraphTy n) {
            return n->nodes.end();
        }

        static ChildIteratorType child_begin(NodeRef nr) {
            return nr->get_nexts().begin();
        }

        static ChildIteratorType child_end(NodeRef nr) {
            return nr->get_nexts().end();
        }
        /*static NodeRef child_it_get(ChildIteratorType&) {

        }

        static std::string Nodekey(NodeRef nr) {
            std::stringstream s;
            s << nr.first.first << "-" << nr.first.second;
            return s.str();
        }

        static const void* NodePointer(NodeRef nr) {
            return nullptr;
        }*/
    };
};





std::string GraphView::creat_graph(const char* dotName)
{
    std::string s;
    llvm::raw_string_ostream Dots(s);
    ExplodedGraph E(*this);
    ExplodedGraph* pE = &E;
    llvm::GraphWriter<ExplodedGraph*> G(Dots, pE, false);
    G.writeGraph(dotName);
    return s;
}


inline std::shared_ptr<TraceInterface> GraphView::mk_explore() {
    return std::make_shared<explorer>(*this);
}


// ===============================================================================================================================


//void gk(State& s, Addr ea, GraphView& gv) {
//
//
//    s.get_trace()->setFlags(CF_traceJmp);
//    s.get_trace()->setFlags(CF_ppStmts);
//    //s.vctx().hook_add(0x551AF328, nullptr, CF_ppStmts);
//    Addr ip = ea;
//    Vex_Kind vkd;
//    std::deque<TR::State::BtsRefType> tmp_branch = s.start();
//    vex_context& vctx = s.vctx();
//
//
//    //if (s.status() == Fork) {
//    //    for (auto one_s : tmp_branch) {
//    //        Addr64 oep = one_s->get_oep();
//    //        State* child = one_s->child();
//
//    //        child->set_trace(std::make_shared<explorer>(gv));
//
//    //        vctx.pool().enqueue([child, oep, &gv] {
//
//    //            gk(*child, oep, gv);
//
//    //            });
//    //    }
//    //}
//
//
//}


void vmp_reback(State& s) {
    GraphView gv(s.vctx());
    gv.explore_block(&s);
    s.vctx().pool().wait();

    gv.simplify();


    gv.ppGraphView(true);
    std::string Dots = gv.creat_graph();
    std::ofstream Dot;
    Dot.open("examplex.dot");
    Dot << Dots;
    Dot.close();

    spdlog::info("state:{}", (std::string)s);
};

inline void TRVexStmtExit::emit(void) const {
    IRBuilder<>* builder;
    Value* v_cmp;
    BasicBlock* bb_then, * bb_else, * bb_origin;

    builder = theGenLLVM->getBuilder();
    bb_origin = builder->GetInsertBlock();
    bb_then = BasicBlock::Create(
        getGlobalContext(), "exit_then",
        bb_origin->getParent());
    bb_else = BasicBlock::Create(
        getGlobalContext(), "exit_else",
        bb_origin->getParent());

    /* evaluate guard condition */
    builder->SetInsertPoint(bb_origin);
    v_cmp = guard->emit();
    builder->CreateCondBr(v_cmp, bb_then, bb_else);

    /* guard condition return, leave this place */
    /* XXX for calls we're going to need some more info */
    builder->SetInsertPoint(bb_then);

    if (jk != Ijk_Boring) {
        /* special exits set exit type */
        theGenLLVM->setExitType((GuestExitType)exit_type);
    }

    auto MB = GV.get_MutiBlocks();
    if (MB.find(dst) != MB.end()) {
        for (auto B : *MB[dst].get()) {
            guest_ptr guest_addr;
            ppIRSB(B.get_irsb_chunk()->get_irsb());
            RBVexSB vsb(GV, guest_addr, B.get_irsb_chunk()->get_irsb());
            vsb.emit_one();
        }
    }
    else {
        builder->CreateRet(
            ConstantInt::get(
                getGlobalContext(),
                APInt(nbits, dst)));
    }


    /* continue on */
    builder->SetInsertPoint(bb_else);
}


