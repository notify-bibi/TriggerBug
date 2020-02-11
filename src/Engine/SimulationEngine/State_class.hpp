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


extern thread_local Pap    pap ;
extern thread_local Addr64   guest_start_of_block ;
extern thread_local bool   is_dynamic_block ;
extern thread_local UChar  ir_temp_trunk[MAX_IRTEMP * sizeof(Vns)];

unsigned char* _n_page_mem(void* pap);

class GraphView;


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
        TRsolver(context& c) :
            z3::solver(mk_tactic_solver_default(c))
            /*z3::solver(c)*/
        {
            m_asserts.reserve(2);
        };
        TRsolver(context& c, solver const& src, translate x) : z3::solver(c, src, x) { m_asserts.reserve(2); }
        void push() { m_solver_snapshot = true; z3::solver::push(); }
        void pop() { z3::solver::pop(); m_solver_snapshot = false; }
        bool is_snapshot() { return m_solver_snapshot; }
        std::vector<Vns>& get_asserts() const { return m_asserts; };
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
        static z3::solver mk_tactic_solver_default(z3::context& c) {
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
            z3::params t_params(c);
            z3::tactic t_tactic(z3::with(z3::tactic(c, "simplify"), t_params) &
                z3::tactic(c, "sat") &
                z3::tactic(c, "solve-eqs") &
                z3::tactic(c, "bit-blast") &
                z3::tactic(c, "smt")
            );
            return t_tactic.mk_solver();
        }
        void use_tactic(z3::tactic&t) {
            *(z3::solver*)(this) = t.mk_solver();
        }
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


template<class BState>
class BranchManager {
    class _Chunk {
        template<class _> friend class BranchManager;
        BranchManager<BState>* m_this;
        _Chunk* m_bk;
        _Chunk* m_fd;
    };

    class Iterator {
        const _Chunk* m_ptr;
        const _Chunk* m_fd;
    public:
        Iterator(const _Chunk *s):m_ptr(s), m_fd(s->m_fd){
        }

        inline bool operator!=(const Iterator& src)
        {
            return m_ptr != src.m_ptr;
        }

        inline void operator++()
        {
            m_ptr = m_fd;
            m_fd= m_fd->m_fd;
        }

        inline BState* operator*() {
            return &m_ptr->m_this->m_state;
        }
    };

    BState& m_state;
    _Chunk m_chunk_link;
    _Chunk m_chunk_branch;

    static void link(_Chunk* cs, _Chunk* branch) {
        _Chunk* fd = cs->m_fd;
        branch->m_bk = cs; branch->m_fd = fd;
        cs->m_fd = branch; fd->m_bk = branch;
    };

public:
    BranchManager(BState& state) :m_state(state) {
        m_chunk_link.m_this = this;
        m_chunk_link.m_bk = &m_chunk_link;
        m_chunk_link.m_fd = &m_chunk_link;
        m_chunk_branch.m_this = this;
        m_chunk_branch.m_bk = &m_chunk_branch;
        m_chunk_branch.m_fd = &m_chunk_branch;
    };

    BranchManager(BState& state, BranchManager<BState>& f_bm) :BranchManager(state) {
        link(&f_bm.m_chunk_branch, &m_chunk_link);
    };

    bool empty() const { return m_chunk_branch.m_bk == &m_chunk_branch; }
    UInt size() const { 
        _Chunk* ptr = m_chunk_branch.m_fd; 
        UInt i;
        for (i = 0; ptr != &m_chunk_branch; i++, ptr = ptr->m_fd) {};
        return i;
    }
    operator BState& () { return m_state; };

    ~BranchManager() {
        vassert(m_chunk_branch.m_bk == &m_chunk_branch);
        vassert(m_chunk_branch.m_fd == &m_chunk_branch);
        _Chunk* bk = m_chunk_link.m_bk; _Chunk* fd = m_chunk_link.m_fd;
        bk->m_fd = fd;
        fd->m_bk = bk;
    }



    Iterator begin() const {
        return Iterator(m_chunk_branch.m_fd);
    }

    Iterator end() const {
        return Iterator(&m_chunk_branch);
    }
};



template<typename ADDR>
class StateAnalyzer;

template<typename ADDR>
class State :public Kernel {
    template<typename ADDR> friend class MEM;
    friend class GraphView;
    template<typename ADDR> friend class StateAnalyzer;

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
    State_Tag   m_status;

public:
    InvocationStack<ADDR>   m_InvokStack;
    TRsolver                solv;
    //客户机寄存器
    Register<REGISTER_LEN>  regs;
    //客户机内存 （多线程设置相同user，不同state设置不同user）
	MEM<ADDR>               mem;
    BranchManager<State<ADDR>> branch;
    std::vector<BranchChunk> branchChunks;

    State(const char* filename, ADDR gse, Bool _need_record) ;
	State(State *father_state, ADDR gse) ;
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

	void compress();//最大化缩合状态 
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
    inline State_Tag status() { return m_status; }
    inline void set_status(State_Tag t) { m_status = t; };
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

    virtual void* mkState(ADDR ges)  { return (State<ADDR>*)ForkState(ges); }
    virtual State_Tag Ijk_call(IRJumpKind){ VPANIC("need to implement the method"); m_status = Death; };
    virtual void  cpu_exception()     { VPANIC("need to implement the method"); m_status = Death; }
    virtual void* ForkState(ADDR ges) { VPANIC("need to implement the method"); return nullptr; }
    virtual bool  StateCompression(State const& next) { return true; }
    virtual void  StateCompressMkSymbol(State const& newState) {  };
    //State::delta maybe changed by callback
    virtual inline State_Tag call_back_hook(Hook_struct const &hs) { return (hs.cb) ? (hs.cb)(this) : Running; }
    
private:

    bool vex_start(Bool first_bkp_pass);

    inline State_Tag _call_back_hook(Hook_struct const& hs) {
        auto ret = call_back_hook(hs);
        solv.check_if_forget_pop();
        return ret;
    }

}; 

template<typename ADDR>
static inline std::ostream& operator<<(std::ostream& out, State<ADDR> const& n) {
    return out << (std::string)n;
}


#endif


