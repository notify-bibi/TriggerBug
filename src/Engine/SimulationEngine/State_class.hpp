/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    State_class.hpp:
Abstract:
    符号变量
Author:
    WXC 2019-05-31.
Revision History:
--*/

#ifndef STATE_CLASS_DEFS
#define STATE_CLASS_DEFS


#include "../engine.hpp"
#include "Variable.hpp"
#include "Register.hpp"
#include "memory.hpp"
#include "tinyxml2/tinyxml2.h"
#include "../Thread_Pool/ThreadPool.hpp"
#include "Kernel.hpp"
#include "IRDirty.hpp"

#define ir_temp ((Vns*)ir_temp_trunk)
extern void* funcDict(void*);
extern void Func_Map_Init();
extern int eval_all(std::vector<Vns>& result, solver& solv, Z3_ast nia);
extern std::string replace(const char* pszSrc, const char* pszOld, const char* pszNew);
extern "C" ULong x86g_use_seg_selector(HWord ldt, HWord gdt, UInt seg_selector, UInt virtual_addr);
extern __m256i  m32_fast[33];
extern __m256i  m32_mask_reverse[33];


extern thread_local void* g_state;
extern thread_local Pap    pap ;
extern thread_local Addr64   guest_start_of_block ;
extern thread_local bool   is_dynamic_block ;
extern thread_local UChar  ir_temp_trunk[MAX_IRTEMP * sizeof(Vns)];

unsigned char* _n_page_mem(void* pap);

class GraphView;


class ForkException {
    std::string m_msg;
    Addr64 m_gaddr;
public:
    ForkException(char const* msg, Addr64 gaddr = 0) :m_msg(msg), m_gaddr(gaddr){ }
    //ForkException(char const* msg) :m_msg(msg), m_gaddr(0) { }
    std::string msg() const {
        return m_msg;
    }
    friend std::ostream& operator<<(std::ostream& out, ForkException const& e);
};
inline std::ostream& operator<<(std::ostream& out, ForkException const& e) { out << e.msg(); return out; }


class BranchChunk {
public:
    Addr64 m_oep;
    Vns  m_sym_addr;
    Vns  m_guard;
    bool m_tof;

    BranchChunk(Addr64 oep, Vns const& sym_addr, Vns const& guard, bool tof) :
        m_oep(oep),
        m_sym_addr(sym_addr),
        m_guard(guard),
        m_tof(tof)
    {}
    ~BranchChunk(){}
};


class TRsolver :public z3::solver{
    template<typename ADDR>
    friend class State;
    friend class BranchChunk;
    friend class StateX86;
    friend class StateAMD64;
    bool                    m_solver_snapshot = false;//if solver::push() m_solver_snapshot = true
    std::vector<Vns>        m_asserts;
    public:
        TRsolver(context& c) :z3::solver(c) { m_asserts.reserve(2); }
        TRsolver(context& c, solver const& src, translate x) : z3::solver(c, src, x) { m_asserts.reserve(2); }
        void push() { m_solver_snapshot = true; z3::solver::push(); }
        void pop() { z3::solver::pop(); m_solver_snapshot = false; }
        bool is_snapshot() { return m_solver_snapshot; }
        Vns getassert(z3::context& ctx);
        Vns getassert();
        //不会保存assert到solver,因为在push之前会进行push
        void add(expr const &e){
            if (!m_solver_snapshot) {
                m_solver_snapshot = true;
                push();
            }
            add_assert(Vns(e, 1), True);
        }
        //不会保存assert到solver,因为在push之前会进行push
        void add(Vns const& e) {
            if (!m_solver_snapshot) {
                m_solver_snapshot = true;
                push();
            }
            add_assert(e, True);
        }
        void check_if_forget_pop() {
            if (m_solver_snapshot) {
                m_solver_snapshot = false;
                pop();
            }
        }
        void add_assert(Vns const& assert, Bool ToF);
        inline void add_assert(Vns const& assert) { add_assert(assert, True); };
        inline void add_assert_eq(Vns const& eqA, Vns const& eqB);
        void add_assert(expr const& assert, Bool ToF) { add_assert(assert, ToF); }
        inline void add_assert(expr const& assert) { add_assert(assert, True); };
        inline void add_assert_eq(expr const& eqA, expr const& eqB) { add_assert_eq(Vns(eqA.ctx(), (Z3_ast)eqA), Vns(eqB.ctx(), (Z3_ast)eqB)); }
        inline operator Z3_context() { return ctx(); }
private:
};

//Functional programming
template<typename ADDR>
class InvocationStack {
    std::queue<ADDR> guest_call_stack;
    std::queue<ADDR> guest_stack;
public:
    inline InvocationStack(){}
    inline InvocationStack(InvocationStack<ADDR> const& fsk) {
        guest_call_stack = fsk.guest_call_stack;
        guest_stack = fsk.guest_stack;
    }
    inline void push(ADDR call_ptr, ADDR bp/*栈底*/) {
        guest_call_stack.push(call_ptr); 
        guest_stack.push(bp);
    }
    inline void pop() {
        guest_call_stack.pop();
        guest_stack.pop();
    }
    template<typename ADDR> friend bool operator==(InvocationStack<ADDR> const& a, InvocationStack<ADDR> const& b);
    void operator=(InvocationStack<ADDR> const& b) {
        guest_call_stack = b.guest_call_stack;
        guest_stack = b.guest_stack;
    }
};

template<typename ADDR>
static inline bool operator==(InvocationStack<ADDR> const& a, InvocationStack<ADDR> const& b) {
    return (a.guest_call_stack == b.guest_call_stack) && (a.guest_stack == b.guest_stack);
}

template<typename ADDR>
class StateCompressNode {
public:
    State<ADDR>* state;
    UInt compress_group;
    UInt State_flag;//0:delete 1:compress 2:Fork State
    std::vector<StateCompressNode<ADDR>*> child_nodes;
    std::vector<State<ADDR>*> avoid_assert_state;
    StateCompressNode(){}
};

template<typename ADDR>
class StateAnalyzer;

template<typename ADDR>
class State :public Kernel {
    template<typename ADDR> friend class MEM;
    friend class GraphView;
    template<typename ADDR> friend class StateAnalyzer;
    template<typename ADDR> friend class InvocationStack;

protected:
    //当前state的入口点
    ADDR        guest_start_ep;
    //客户机state的eip（计数器eip）
    ADDR        guest_start;
private:
    bool        m_dirty_vex_mode = false;
    DirtyCtx    m_dctx = nullptr;
    VexArchInfo *vai_guest,  *vai_host;

    Bool        need_record;
    UInt        m_z3_bv_const_n;
    std::mutex  m_state_lock;
    ADDR        m_delta;

public:
    Kernel* m_father_state;
    State_Tag               status;
    InvocationStack<ADDR>   m_InvokStack;
    TRsolver                solv;
    //客户机寄存器
    Register<REGISTER_LEN>  regs;
    //客户机内存 （多线程设置相同user，不同state设置不同user）
	MEM<ADDR>               mem;
    std::vector<State*>     branch;
    std::vector<BranchChunk> branchChunks;

    State(const char* filename, ADDR gse, Bool _need_record) ;
	State(State *father_state, ADDR gse) ;
    void setSolver(z3::tactic const& tactic) { 
        vassert(m_father_state == nullptr);
        solv.reset();
        (solver)solv = tactic.mk_solver(); 
    };
    void read_mem_dump(const char*);

	~State() ;
    void init_irTemp();
    void clear_irTemp();
	inline IRSB* BB2IR();
    void start(Bool first_bkp_pass);
    void branchGo();
    State* mkChildState(BranchChunk const&);
    //ip = ip + offset
    inline void hook_pass(ADDR offset) { m_delta = offset; };

	void compress(ADDR Target_Addr, State_Tag Target_Tag, std::vector<State_Tag> &avoid);//最大化缩合状态 
	inline Vns tIRExpr(IRExpr*); 
    Vns CCall(IRCallee *cee, IRExpr **exp_args, IRType ty);
	inline Vns ILGop(IRLoadG *lg);

    Vns mk_int_const(UShort nbit);
    Vns mk_int_const(UShort n, UShort nbit);
    UInt getStr(std::stringstream& st, ADDR addr);
    inline operator MEM<ADDR>& () { return mem; }
    inline operator Register<REGISTER_LEN>& () { return regs; }
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

    virtual inline void traceStart() { return; };
    virtual inline void traceFinish() { return; };
    virtual inline void traceIRSB(IRSB*) { return; };
    virtual inline void traceIrsbEnd(IRSB*) { return; };
    virtual inline void traceIRStmtEnd(IRStmt*) { return; };

    virtual State_Tag   Ijk_call(IRJumpKind){ VPANIC("need to implement the method"); status = Death; };
    virtual void        cpu_exception()     { VPANIC("need to implement the method"); status = Death; }
    virtual State*      ForkState(ADDR ges) { VPANIC("need to implement the method"); return nullptr; }
    virtual bool        StateCompression(State const& next) { return true; }
    virtual void        StateCompressMkSymbol(State const& newState) {  };
    //State::delta maybe changed by callback
    virtual inline State_Tag call_back_hook(Hook_struct const &hs) { return (hs.cb) ? (hs.cb)(this) : Running; }
    
private:
    inline State_Tag _call_back_hook(Hook_struct const& hs) {
        auto ret = call_back_hook(hs);
        solv.check_if_forget_pop();
        return ret;
    }

    inline bool _StateCompression(State<ADDR> const& next) {
        bool ret = m_InvokStack == next.m_InvokStack;// 压缩条件
        return ret && StateCompression(next);//支持扩展条件
    }

    template<typename ADDR> friend static UInt divide_into_groups(std::vector<State<ADDR>*>& group, State<ADDR>* s);
    
    inline void _StateCompressMkSymbol(State<ADDR> const& newState) {
        m_InvokStack = newState.m_InvokStack;// 使其满足压缩条件
        StateCompressMkSymbol(newState);//支持
    }

    bool treeCompress(Vns& avoid_asserts_ret, bool &has_branch,
        std::hash_map<ADDR, Vns>& change_map_ret,
        StateCompressNode<ADDR>* SCNode, UInt group, TRcontext& ctx, UInt deep);

    void get_write_map(
        std::hash_map<ADDR, Vns>& change_map_ret, TRcontext& ctx
    );

    StateCompressNode<ADDR>* mkCompressTree(
        std::vector<State*>& group,
        ADDR Target_Addr, State_Tag Target_Tag, std::vector<State_Tag>& avoid
    );

    void set_changes(std::hash_map<ADDR, Vns>& change_map_ret);
    void set_changes(std::hash_map<ADDR, Vns>& change_map_ret, z3::solver::translate);
}; 

template<typename ADDR>
static inline std::ostream& operator<<(std::ostream& out, State<ADDR> const& n) {
    return out << (std::string)n;
}

template <typename ADDR, class TC>
class StatePrinter : public TC {
    friend GraphView;
    TRControlFlags trtraceflags;

public:
    inline bool getFlag(TRControlFlags t) const { return trtraceflags & t; }
    inline void setFlag(TRControlFlags t) { *(ULong*)&trtraceflags |= t; }
    inline void unsetFlag(TRControlFlags t) { *(ULong*)&trtraceflags &= ~t; };
    inline TRControlFlags gtrtraceflags() { return trtraceflags; }
public:
    StatePrinter(const char* filename, ADDR gse, Bool _need_record) : 
        TC(filename, gse, _need_record),
        trtraceflags(CF_None) {
        if (doc_debug) {
            bool traceState = false, traceJmp = false, ppStmts = false, TraceSymbolic = false;
            auto _ppStmts = doc_debug->FirstChildElement("ppStmts");
            auto _TraceState = doc_debug->FirstChildElement("TraceState");
            auto _TraceJmp = doc_debug->FirstChildElement("TraceJmp");
            auto _TraceSymbolic = doc_debug->FirstChildElement("TraceSymbolic");

            if (_TraceState) _TraceState->QueryBoolText(&traceState);
            if (_TraceJmp) _TraceJmp->QueryBoolText(&traceJmp);
            if (_ppStmts) _ppStmts->QueryBoolText(&ppStmts);
            if (_TraceSymbolic) _TraceSymbolic->QueryBoolText(&TraceSymbolic);
            if (traceState) setFlag(CF_traceState);
            if (traceJmp) setFlag(CF_traceJmp);
            if (ppStmts) setFlag(CF_ppStmts);
            if (TraceSymbolic) setFlag(CF_TraceSymbolic);
        }
    };

    StatePrinter(StatePrinter* father_state, ADDR gse) : TC(father_state, gse) , trtraceflags(father_state->trtraceflags) {};


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
    
    void   traceIRStmtEnd(IRStmt* s) {
        if (getFlag(CF_ppStmts)) {
            if (s->tag == Ist_WrTmp) {
                UInt tmp = s->Ist.WrTmp.tmp;
                vex_printf("t%u = ", tmp);
                std::cout << ir_temp[tmp] ;
                vex_printf(" = ");
                ppIRExpr(s->Ist.WrTmp.data);
            }
            else {
                ppIRStmt(s);
            }
            vex_printf("\n");
        }
    };

    void   traceIRSB(IRSB* bb) {
        if (getFlag(CF_traceJmp)) {
            vex_printf("Jmp: %llx \n", guest_start);
        }
    };


    virtual State<ADDR>* ForkState(ADDR ges) { return new StatePrinter<ADDR, TC>(this, ges); };
    virtual State_Tag call_back_hook(Hook_struct const& hs) { setFlag(hs.cflag); return (hs.cb) ? (hs.cb)(this) : Running; }
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
