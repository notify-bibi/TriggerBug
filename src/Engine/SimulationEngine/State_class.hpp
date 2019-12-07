#ifndef State_class_defs
#define State_class_defs


#include "../engine.hpp"
#include "Variable.hpp"
#include "Register.hpp"
#include "memory.hpp"
#include "tinyxml2/tinyxml2.h"
#include "../Thread_Pool/ThreadPool.hpp"

#define ir_temp ((Vns*)ir_temp_trunk)
extern void* funcDict(void*);
extern void Func_Map_Init();
extern int eval_all(std::vector<Vns>& result, solver& solv, Z3_ast nia);
extern std::string replace(const char* pszSrc, const char* pszOld, const char* pszNew);
extern "C" ULong x86g_use_seg_selector(HWord ldt, HWord gdt, UInt seg_selector, UInt virtual_addr);
extern __m256i  m32_fast[33];
extern __m256i  m32_mask_reverse[33];


extern thread_local State* g_state ;
extern thread_local bool   ret_is_ast ;
extern thread_local Pap    pap ;
extern thread_local ADDR   guest_start_of_block ;
extern thread_local bool   is_dynamic_block ;
extern thread_local UChar  ir_temp_trunk[MAX_IRTEMP * sizeof(Vns)];


class State;
class GraphView;


typedef enum :UChar {
    unknowSystem = 0b00,
    linux,
    windows
}GuestSystem;


typedef enum :ULong {
    CF_None = 0,
    CF_ppStmts = 1ull,
    CF_traceJmp = 1ull << 1,
    CF_traceState = 1ull << 2,
    CF_TraceSymbolic = 1ull << 3,
    CF_PassSigSEGV = 1ull << 4,
}TRControlFlags;


typedef struct _Hook {
    TRtype::Hook_CB cb;
    UChar original;
    TRControlFlags cflag;
}Hook_struct;


class StatetTraceFlag {
    friend GraphView;
    TRControlFlags trtraceflags;

public:
    StatetTraceFlag():trtraceflags(CF_None) {}
    StatetTraceFlag(StatetTraceFlag& f): trtraceflags(f.trtraceflags) { }
    inline bool getFlag(TRControlFlags t) const { return trtraceflags & t;}
    inline void setFlag(TRControlFlags t) { *(ULong*)&trtraceflags |= t; }
    inline void unsetFlag(TRControlFlags t) { *(ULong*)&trtraceflags &= ~t; };
    inline TRControlFlags gtrtraceflags() { return trtraceflags; }
};


class Vex_Info :public StatetTraceFlag {
    friend GraphView;
private:
    static tinyxml2::XMLDocument doc;
    static tinyxml2::XMLError err;
    static tinyxml2::XMLElement* doc_TriggerBug;
public:
    static Int iropt_level;
    static UInt guest_max_insns;
    static VexRegisterUpdates iropt_register_updates_default;
    static VexArch	guest;
    static GuestSystem guest_system;
    static const char* MemoryDumpPath;
    static tinyxml2::XMLElement* doc_VexControl;
    static tinyxml2::XMLElement* doc_debug;
    static UInt MaxThreadsNum;
    static Int traceflags;
    UInt gRegsIpOffset();
protected:
    thread_local static VexGuestExtents     vge_chunk;
    thread_local static VexTranslateArgs    vta_chunk;

protected:
    Vex_Info(const char* filename) :StatetTraceFlag() { init_vex_info(filename); }
    Vex_Info(Vex_Info& f) :StatetTraceFlag(f) {}

private:

    static UInt _gtraceflags();
    static tinyxml2::XMLError loadFile(const char* filename);
    static void _gGuestArch();
    static void _gMemoryDumpPath();
    static void _gVexArchSystem();
    static void _giropt_register_updates_default();
    static void _giropt_level();
    static void _gguest_max_insns();
    static void _gMaxThreadsNum();
    void init_vex_info(const char* filename);

};


class BranchChunk {
public:
    ADDR m_oep;
    Vns  m_sym_addr;
    Vns  m_guard;
    bool m_tof;

    BranchChunk(ADDR oep, Vns const& sym_addr, Vns const& guard, bool tof) :
        m_oep(oep),
        m_sym_addr(sym_addr),
        m_guard(guard),
        m_tof(tof)
    {
    }
    State* getState(State& fstate);
    ~BranchChunk(){}
};


typedef struct ChangeView {
    State* elders;
    ChangeView* front;
}ChangeView;


class TRsolver :public z3::solver{
    friend class State;
    bool                    m_solver_snapshot = false;
    std::vector<Vns>        m_asserts;
    public:
        TRsolver(context& c) :z3::solver(c) { m_asserts.reserve(2); }
        TRsolver(context& c, solver const& src, translate x) : z3::solver(c, src, x) { m_asserts.reserve(2); }
        void push() { m_solver_snapshot = true; z3::solver::push(); }
        void pop() { z3::solver::pop(); m_solver_snapshot = false; }
        bool is_snapshot() { return m_solver_snapshot; }
};


class StateAnalyzer;
class State:public Vex_Info {
    friend MEM;
    friend GraphView;
    friend StateAnalyzer;

protected:
    static std::hash_map<ADDR, Hook_struct> CallBackDict;
    static std::hash_map<ADDR/*static table base*/, TRtype::TableIdx_CB> TableIdxDict;

    ADDR guest_start_ep;
    ADDR guest_start;
	void *VexGuestARCHState;

private:
    VexArchInfo *vai_guest,  *vai_host;

    Bool need_record;
    int  replace_const;
    bool unit_lock;
    ADDR delta;

public:
    static ThreadPool*      pool;
    State*                  m_father_state;
    State_Tag               status;
    TRcontext               m_ctx;
    TRsolver                solv;
public:
    //客户机寄存器
	Register<REGISTER_LEN>  regs;
    //客户机内存 （多线程设置相同user，不同state设置不同user）
	MEM                     mem;
    std::vector<State*>     branch;
    std::vector<BranchChunk> branchChunks;


    State(const char* filename, ADDR gse, Bool _need_record) ;
	State(State *father_state, ADDR gse) ;
    void setSolver(z3::tactic const& tactic) { 
        solv.reset();
        (solver)solv = tactic.mk_solver(); 
    };
    void read_mem_dump(const char*);

	~State() ;
    static void init_irTemp();
    static void clear_irTemp();
    void initVexEngine();
	inline IRSB* BB2IR();
	void add_assert(Vns &assert, Bool ToF);
    inline void add_assert(Vns& assert) { add_assert(assert, True); };
	inline void add_assert_eq(Vns &eqA, Vns &eqB);
    void start(Bool first_bkp_pass);
    void branchGo();
    //ip = ip + offset
    inline void hook_pass(ADDR offset) { delta = offset; };


	void compress(ADDR Target_Addr, State_Tag Target_Tag, std::vector<State_Tag> &avoid);//最大化缩合状态 
    Vns getassert(z3::context &ctx);
	inline Vns tIRExpr(IRExpr*); 
    Vns CCall(IRCallee *cee, IRExpr **exp_args, IRType ty);
    static Vns T_Unop(context & m_ctx, IROp, Vns const&);
    static Vns T_Binop(context & m_ctx, IROp, Vns const&, Vns const&);
    static Vns T_Triop(context & m_ctx, IROp, Vns const&, Vns const&, Vns const&);
    static Vns T_Qop(context & m_ctx, IROp, Vns const&, Vns const&, Vns const&, Vns const&);
	inline Vns ILGop(IRLoadG *lg);

    Vns get_int_const(UShort nbit);
    Vns get_int_const(UShort n, UShort nbit);
    UInt getStr(std::stringstream& st, ADDR addr);
    //read static_table from symbolic address  定义 index 和 该常量数组 之间的关系 不然z3只能逐一爆破 如DES的4个静态表
    static inline void idx2Value_Decl_add(Addr64 addr, TRtype::TableIdx_CB func) { TableIdxDict[addr] = func; };
    static inline void idx2Value_Decl_del(Addr64 addr, TRtype::TableIdx_CB func) { TableIdxDict.erase(TableIdxDict.find(addr)); };
    Z3_ast idx2Value(ADDR base, Z3_ast idx);

    inline operator context& () { return m_ctx; }
    inline operator Z3_context() const { return m_ctx; }
    inline operator MEM& () { return mem; }
    inline operator Register<REGISTER_LEN>&() { return regs; }
    inline ADDR get_cpu_ip() { return guest_start; }
    inline ADDR get_state_ep() { return guest_start_ep; }
    inline ADDR get_start_of_block() { return guest_start_of_block; }
	operator std::string() const;


    static void pushState(State& s) {
        pool->enqueue([&s] {
            s.start(True);
            });
    }

    //backpoint add
    void hook_add(ADDR addr, TRtype::Hook_CB func = nullptr, TRControlFlags cflag = CF_None)
    {
        if (CallBackDict.find(addr) == CallBackDict.end()) {
            auto P = mem.getMemPage(addr);
            if (!P) {
                vex_printf("hook_add: mem access error %p not mapped", addr);
            }
            else {
                CallBackDict[addr] = Hook_struct{ func ,P->unit->m_bytes[addr & 0xfff] , cflag };
                P->unit->m_bytes[addr & 0xfff] = 0xCC;
            }
        }
        else {
            if (func){
                CallBackDict[addr].cb = func;
            }
            if (cflag != CF_None) {
                CallBackDict[addr].cflag = cflag;
            }
        }
    }
    bool get_hook(Hook_struct& hs, ADDR addr);
    void hook_del(ADDR addr, TRtype::Hook_CB func);
    //interface :

    virtual inline void   traceStart() { return; };
    virtual inline void   traceFinish() { return; };
    virtual inline void   traceIRSB(IRSB*) { return; };
    virtual inline void   traceIRStmtBegin(IRStmt*) { return; };
    virtual inline void   traceIRStmtEnd(IRStmt*) { return; };

    virtual inline State_Tag Ijk_call(IRJumpKind) { return Death; };
    virtual inline void   cpu_exception() { status = Death; }
    virtual inline State* ForkState(ADDR ges) { return nullptr; }

private:
    inline Bool treeCompress(TRcontext& ctx, ADDR Target_Addr, State_Tag Target_Tag, std::vector<State_Tag>& avoid, ChangeView& change_view, std::hash_map<ULong, Vns>& change_map, std::hash_map<UShort, Vns>& regs_change_map);

}; 


static inline std::ostream& operator<<(std::ostream& out, State const& n) {
    return out << (std::string)n;
}

template <class TC>
class StatePrinter : public TC {
public:
    StatePrinter(const char* filename, ADDR gse, Bool _need_record) : TC(filename, gse, _need_record){};

    StatePrinter(StatePrinter* father_state, ADDR gse) : TC(father_state, gse) {};


    void spIRExpr(const IRExpr* e);
    void spIRTemp(IRTemp tmp);
    void spIRPutI(const IRPutI* puti);
    void spIRStmt(const IRStmt* s);

    void   traceStart() {
        if (getFlag(CF_traceState))
            std::cout << "\n+++++++++++++++ Thread ID: " << GetCurrentThreadId() << "  address: " << std::hex << guest_start << "  Started +++++++++++++++\n" << std::endl;
    };

    void   traceFinish() {
        if (getFlag(CF_traceState)) {
            if (status == Fork) {
                vex_printf("Fork from: %p to:{ ", guest_start);
                for (BranchChunk& bc : branchChunks) {
                    vex_printf(" %p", bc.m_oep);
                }
                vex_printf(" };", guest_start);
            }
            std::cout << "\n+++++++++++++++ Thread ID: " << GetCurrentThreadId() << "  address: " << std::hex << guest_start << "  OVER +++++++++++++++\n" << std::endl;
        }
    }
    
    void   traceIRStmtBegin(IRStmt* s) {
        if (getFlag(CF_ppStmts)) {
            ppIRStmt(s);
        }
    };
    void   traceIRStmtEnd(IRStmt* s) {
        if (getFlag(CF_ppStmts)) {
            if (s->tag == Ist_WrTmp) {
                std::cout << ir_temp[s->Ist.WrTmp.tmp] << std::endl;
            }
            else {
                vex_printf("\n");
            }
        }
    };

    void   traceIRSB(IRSB* bb) {
        if (getFlag(CF_traceJmp)) {
            vex_printf("Jmp: %llx \n", guest_start);
        }
    };


    virtual State* ForkState(ADDR ges) {
        return new StatePrinter<TC>(this, ges);
    };

};








#endif



/*Legal parameters are :
  ctrl_c(bool) (default: true)
  dump_benchmarks(bool) (default: false)
  dump_models(bool) (default: false)
  elim_01(bool) (default: true)
  enable_sat(bool) (default: true)
  enable_sls(bool) (default: false)
  maxlex.enable(bool) (default: true)
  maxres.add_upper_bound_block(bool) (default: false)
  maxres.hill_climb(bool) (default: true)
  maxres.max_core_size(unsigned int) (default: 3)
  maxres.max_correction_set_size(unsigned int) (default: 3)
  maxres.max_num_cores(unsigned int) (default: 4294967295)
  maxres.maximize_assignment(bool) (default: false)
  maxres.pivot_on_correction_set(bool) (default: true)
  maxres.wmax(bool) (default: false)
  maxsat_engine(symbol) (default: maxres)
  optsmt_engine(symbol) (default: basic)
  pb.compile_equality(bool) (default: false)
  pp.neat(bool) (default: true)
  priority(symbol) (default: lex)
  rlimit(unsigned int) (default: 0)
  solution_prefix(symbol) (default:)
  timeout(unsigned int) (default: 4294967295)
*/
