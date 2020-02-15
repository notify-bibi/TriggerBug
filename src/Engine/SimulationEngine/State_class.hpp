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
        std::vector<Vns> const & get_asserts() const { return m_asserts; };
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


namespace cmpr {
    template<class CompressClass, typename StateStatus>
    class CmprsContext;

    template<class STATEinterface, class CompressClass, typename StateStatus>
    class Compress;

}

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

    State(const char* filename, ADDR gse, Bool _need_record) ;
	State(State *father_state, ADDR gse) ;
    void read_mem_dump(const char*);

	~State() ;
    void init_irTemp();
    void clear_irTemp();
	inline IRSB* BB2IR();
    void start(Bool first_bkp_pass);
    void branchGo();
    //ip = ip + offset
    inline void hook_pass(ADDR offset) { m_delta = offset; };

    cmpr::CmprsContext<State<ADDR>, State_Tag> cmprContext(ADDR target_addr, State_Tag tag) { return cmpr::CmprsContext<State<ADDR>, State_Tag>(m_ctx, target_addr, tag); }
    void compress(cmpr::CmprsContext<State<ADDR>, State_Tag> &ctx);//最大化缩合状态 
	inline Vns tIRExpr(IRExpr*); 
    Vns dirty_call(IRCallee* cee, IRExpr** exp_args, IRType ty){
        getDirtyVexCtx();
        dirty_ccall<ADDR>(m_dctx, cee, exp_args);
        return dirty_result<ADDR>(m_dctx, ty);
    }
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
    DirtyCtx getDirtyVexCtx(){
        if (!m_dirty_vex_mode) {
            m_dirty_vex_mode = true;
            m_dctx = dirty_context(this);
        }
        return m_dctx;
    }

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



template<typename ADDR>
class StateCmprsInterface;

//  分支合并的压缩算法 

namespace cmpr {
    struct ignore{};
    extern thread_local Z3_context thread_z3_ctx;

    static Vns logic_and(std::vector<Vns> const& v) {
        Z3_context ctx = v[0];
        UInt size = v.size();
        vassert(size > 0);
        if (size == 1) return v[0];
        Z3_ast* list = new Z3_ast[size];
        Z3_ast* ptr = list;
        for (Vns const& ass : v) { *ptr++ = ass; }
        return Vns(ctx, Z3_mk_and(ctx, size, list), 1);
    }

    static Vns logic_or(std::vector<Vns> const& v) {
        Z3_context ctx = v[0];
        UInt size = v.size();
        vassert(size > 0);
        if (size == 1) return v[0];
        Z3_ast* list = new Z3_ast[size];
        Z3_ast* ptr = list;
        for (Vns const& ass : v) { *ptr++ = ass; }
        return Vns(ctx, Z3_mk_or(ctx, size, list), 1);
    }

    class GPMana {
        Z3_context m_ctx;
        struct _m_vec_ {
            bool is_ast;
            union { Z3_ast ast; ULong data; } value;
            Z3_ast* m_maps_ass;
            UInt m_maps_ass_idx;
            struct _m_vec_* sort;
        }*m_vec;
        struct _m_vec_* m_sort;

        UInt m_idx = 0;
        UInt m_size;

        Vns vec2ast(struct _m_vec_* v) const {
            return v->is_ast ? Vns(m_ctx, v->value.ast, 64) : Vns(m_ctx, v->value.data);
        }

        Vns _get(struct _m_vec_* vec) const {
            vassert(vec->m_maps_ass_idx > 0);
            Vns guard = Vns(m_ctx, vec->m_maps_ass_idx == 1 ? vec->m_maps_ass[0] : Z3_mk_or(m_ctx, vec->m_maps_ass_idx, vec->m_maps_ass), 1);

            return vec->sort ? ite(guard, vec2ast(vec), _get(vec->sort)) : vec2ast(vec);
        }

        void check() {
            if (m_idx >= m_size) {
                vassert(m_idx == m_size);
                UInt new_size = m_size * 2;
                m_vec = (_m_vec_*)realloc(m_vec, sizeof(_m_vec_) * new_size);
                for (struct _m_vec_* vec = m_sort; vec; vec = vec->sort) {
                    if (vec->m_maps_ass)
                        vec->m_maps_ass = (Z3_ast*)realloc(vec->m_maps_ass, new_size * sizeof(Z3_ast));
                }
                m_size = new_size;
            }
        }
    public:

        GPMana() :GPMana(thread_z3_ctx, 16) {  };

        GPMana(Z3_context ctx, UInt size) :m_size(size), m_ctx(ctx), m_sort(nullptr) {
            m_vec = (_m_vec_*)malloc(sizeof(_m_vec_) * size);
            memset(m_vec, 0, sizeof(_m_vec_) * m_size);
        }

        GPMana(const GPMana& gp) :GPMana(gp.m_ctx, gp.m_size) {
            m_sort = m_vec;
            m_idx = gp.m_idx;
            UInt idx = 0;
            struct _m_vec_* this_vec = nullptr;
            for (struct _m_vec_* vec = gp.m_sort; vec; vec = vec->sort, idx++) {
                this_vec = &m_vec[idx];
                if (vec->m_maps_ass_idx) {
                    if (!this_vec->m_maps_ass) { this_vec->m_maps_ass = new Z3_ast[m_size]; }
                    for (UInt i = 0; i < vec->m_maps_ass_idx; i++) {
                        this_vec->m_maps_ass[i] = vec->m_maps_ass[i];
                        Z3_inc_ref(m_ctx, vec->m_maps_ass[i]);
                    }
                }
                this_vec->sort = &m_vec[idx + 1];
                this_vec->is_ast = vec->is_ast;
                this_vec->m_maps_ass_idx = vec->m_maps_ass_idx;
                if (this_vec->is_ast) {
                    this_vec->value.ast = vec->value.ast;
                    Z3_inc_ref(m_ctx, this_vec->value.ast);
                }
                else {
                    this_vec->value.data = vec->value.data;
                }
            }
            if (this_vec) {
                this_vec->sort = nullptr;
            }
            else {
                m_sort = nullptr;
            }
        }

        void operator=(const GPMana& gp)
        {
            this->~GPMana();
            this->GPMana::GPMana(gp);
        }


        void add(Vns const& ass, Vns const& v) {
            if (v.real()) add((Z3_ast)ass, (ULong)v); else  add((Z3_ast)ass, (Z3_ast)v);
        }

        void add(Z3_ast ass, Z3_ast v) {
            check();
            bool find = false;
            struct _m_vec_* vec = m_sort;
            struct _m_vec_* prv = nullptr;
            for (; vec; prv = vec, vec = vec->sort) {
                if (vec->is_ast && vec->value.ast == v) {
                    find = true;
                    break;
                }
            }
            if (!vec) {
                vec = &m_vec[m_idx++];
            }
            if (!find) {
                vec->is_ast = true;
                vec->value.ast = v;
                Z3_inc_ref(m_ctx, v);
                struct _m_vec_* next = m_sort;
                vec->sort = next;
                m_sort = vec;
            }
            if (!vec->m_maps_ass) { vec->m_maps_ass = (Z3_ast*)malloc(sizeof(Z3_ast) * m_size); };
            vec->m_maps_ass[vec->m_maps_ass_idx++] = ass;
            Z3_inc_ref(m_ctx, ass);
            if (find) mk_sort(prv, vec);
        }

        void add(Z3_ast ass, ULong v) {
            check();
            bool find = false;
            struct _m_vec_* vec = m_sort;
            struct _m_vec_* prv = nullptr;
            for (; vec; prv = vec, vec = vec->sort) {
                if (!vec->is_ast && vec->value.data == v) {
                    find = true;
                    break;
                }
            }
            if (!vec) {
                vec = &m_vec[m_idx++];
            }
            if (!find) {
                vec->value.data = v;
                vec->is_ast = false;
                struct _m_vec_* next = m_sort;
                vec->sort = next;
                m_sort = vec;
            }
            if (!vec->m_maps_ass) { vec->m_maps_ass = (Z3_ast*)malloc(sizeof(Z3_ast) * m_size); }
            vec->m_maps_ass[vec->m_maps_ass_idx++] = ass;
            Z3_inc_ref(m_ctx, ass);
            if (find) mk_sort(prv, vec);
        }

        void mk_sort(struct _m_vec_* prv, _m_vec_* new_vec) {
            //unlink
            if (new_vec->sort) {
                if (new_vec->m_maps_ass_idx > new_vec->sort->m_maps_ass_idx) {
                    if (prv) {
                        prv->sort = new_vec->sort;
                    }
                    else {
                        m_sort = new_vec->sort;
                    }
                }
                else {
                    return;
                }
            }
            //into
            struct _m_vec_* vec = prv ? prv->sort : m_sort;
            for (; vec; prv = vec, vec = vec->sort) {
                if (new_vec->m_maps_ass_idx <= vec->m_maps_ass_idx) {
                    prv->sort = new_vec;
                    new_vec->sort = vec;
                    return;
                }
            }
            prv->sort = new_vec;
            new_vec->sort = nullptr;
        }


        Vns get() const {
            return _get(m_sort);
        }

        ~GPMana() {
            for (struct _m_vec_* vec = m_sort; vec; vec = vec->sort) {
                for (UInt idx = 0; idx < vec->m_maps_ass_idx; idx++) {
                    Z3_dec_ref(m_ctx, vec->m_maps_ass[idx]);
                }
                if (vec->is_ast) Z3_dec_ref(m_ctx, vec->value.ast);
                free(vec->m_maps_ass);
                vec->m_maps_ass = nullptr;
            }
            free(m_vec);
        }
    };

    typedef enum :Int {
        //子节点
        Fork_Node = -3,
        //叶子节点
        Avoid_Node,
        Survive_Node,
        //target node: 0-n
    }StateType;


    template<class CompressClass, typename StateStatus>
    class CmprsContext {
        Addr64 m_target_addr;
        StateStatus m_target_tag;
        std::vector<StateStatus> m_avoid;
        std::vector<CompressClass*> m_group;
        TRcontext& m_z3_target_ctx;
    public:
        CmprsContext(TRcontext& target_ctx, Addr64 target_addr, StateStatus ttag)
            :m_target_addr(target_addr), m_target_tag(ttag), m_z3_target_ctx(target_ctx)
        {
            thread_z3_ctx = target_ctx;
        }
        void add_avoid(StateStatus avoid_tag) { m_avoid.emplace_back(avoid_tag); };
        bool is_avoid(StateStatus tag) { return std::find(m_avoid.begin(), m_avoid.end(), tag) != m_avoid.end(); }
        Addr64 get_target_addr() { return m_target_addr; }
        std::vector<CompressClass*>& group() const { return m_group; }
        inline TRcontext& ctx() { return m_z3_target_ctx; }
        inline operator TRcontext& () { return m_z3_target_ctx; }
    };





    template<class STATEinterface>
    class CmprsFork;
    template<class STATEinterface>
    class CmprsTarget;



    template<class STATEinterface>
    class CmprsAvoid :public STATEinterface {
    public:
        template<class _CTX, class _S>
        CmprsAvoid(_CTX& ctx, _S& s) :STATEinterface(ctx, s, Avoid_Node) { }
        ~CmprsAvoid() override { del_obj(); }
    };



    template<class STATEinterface>
    class CmprsSurvive :public STATEinterface {
    public:
        template<class _CTX, class _S>
        CmprsSurvive(_CTX& ctx, _S& s) :STATEinterface(ctx, s, Survive_Node) { }
        ~CmprsSurvive() override { };
    };




    template<typename STATEinterface>
    class CmprsTarget :public STATEinterface {
        UInt m_group_id;

    public:
        template<class _CTX, class _S>
        CmprsTarget(_CTX& ctx, _S& s, Int ty) :STATEinterface(ctx, s, (StateType)ty) {
            vassert(ty >= 0);
        };
        CmprsTarget<STATEinterface>& get_target_node() override { return *this; }
        ~CmprsTarget() override { del_obj(); }
    };



    template<class STATEinterface /*= StateCmprsInterface<Addr64>*/>
    class CmprsFork :public STATEinterface {
        template<class STATEinterface, class CompressClass, typename StateStatus> friend class Compress;
        StateType m_compr_ty;
        std::vector<STATEinterface*> m_child_nodes;
        bool m_has_survive = false;
        bool __m_has_survive__ = false;
        std::vector<Int> m_target_counts;
    public:
        template<class _CTX, class _S>
        CmprsFork(_CTX& ctx, _S& s, bool) :CmprsFork(ctx, s) { m_has_survive = true; }
        template<class _CTX, class _S>
        CmprsFork(_CTX& ctx, _S& s) : STATEinterface(ctx, s, Fork_Node) {
            vassert(!branch().empty());
            m_child_nodes.reserve(branch().size());
            for (auto bstate : branch()) {
                STATEinterface* ns = mk(bstate, tag(bstate));
                m_child_nodes.emplace_back(ns);
                if (ns->type() == Survive_Node) {
                    m_has_survive = true;
                }
                if (ns->type() == Fork_Node && ns->has_survive()) {
                    m_has_survive = true;
                }
                if (ns->type() == Fork_Node) {
                    UInt max = ns->get_fork_node().m_target_counts.size();
                    if (max >= m_target_counts.size()) {
                        for (Int g = m_target_counts.size(); g <= max; g++) {
                            m_target_counts.emplace_back(0);
                        }
                    }
                    for (Int p = 0; p < max; p++) {
                        m_target_counts[p] += ns->get_fork_node().target_counts(p);
                    }
                }
                if (ns->type() >= 0) {
                    if (ns->type() >= m_target_counts.size()) {
                        for (Int p = m_target_counts.size(); p <= ns->type(); p++) {
                            m_target_counts.emplace_back(0);
                        }
                    }
                    m_target_counts[ns->type()] += 1;
                }
            }
            __m_has_survive__ = m_has_survive;
        }
        

        bool has_survive(struct ignore)  { return __m_has_survive__; }

        bool has_survive() override { return m_has_survive; }

        UInt target_counts(Int group) const {
            if (group >= m_target_counts.size()) {
                return 0;
            }
            return m_target_counts[group];
        }

        inline std::vector<STATEinterface*>& child_nodes() { return m_child_nodes; }

        inline STATEinterface& operator[](Int idx) { return child_nodes[idx]; }

        CmprsFork<STATEinterface>& get_fork_node() override { return *this; }

        ~CmprsFork() override {
            for (auto s : m_child_nodes) {
                delete s;
            };
            if (!has_survive()) del_obj();
        }
    };



    template<class STATEinterface, class CompressClass, typename StateStatus>
    class Compress {
        CmprsContext<CompressClass, StateStatus>& m_ctx;
        CmprsFork<STATEinterface> m_node;

        class Iterator {
            friend class Compress;
            Compress& m_c;
            UInt m_it_group;
            UInt m_group_max;

            //state compression results
            class StateRes {
                friend class Compress::Iterator;
                Compress& m_c;
                UInt m_group;
                Vns m_assert;
                std::hash_map<Addr64, GPMana> m_changes;

                StateRes(const StateRes& ass) = delete;
                void operator =(const StateRes& ass) = delete;
                StateRes(Compress const& c, UInt group) :m_c(c), m_group(group),
                    m_assert(m_c.avoid_asserts(m_c.m_node, m_group))
                {
                    m_c.treeCompress(m_changes, m_c.m_node, m_group);
                }
            public:
                inline std::hash_map<Addr64, GPMana> const& changes() { return m_changes; }
                inline Vns conditions() const { return m_assert; }
            };


            Iterator(const Iterator& ass) = delete;
            void operator =(const Iterator& ass) = delete;
        public:

            Iterator(Compress const& c) :m_c(c), m_it_group(0) {
                m_group_max = m_c.m_ctx.group().size();
            }
            inline bool operator!=(const Iterator& src) { return m_it_group != src.m_group_max; }
            inline void operator++() { m_it_group++; }
            inline StateRes operator*() { return StateRes(m_c, m_it_group); }
            inline UInt group_max() { return m_group_max; }
        };

        Compress(const Compress& ass) = delete;
        void operator =(const Compress& ass) = delete;
    public:

        Compress(
            CmprsContext<CompressClass, StateStatus>& ctx,
            CompressClass& state
        ) :
            m_ctx(ctx), m_node(m_ctx, state, false)
        {

        }
        inline bool has_survive() { return m_node.has_survive(ignore {}); }
        inline operator TRcontext& () { return m_z3_target_ctx; }
        Iterator begin() const { return Iterator(*this); }
        Iterator end() const { return Iterator(*this); }
        void clear_nodes() {
            for (auto s : m_node.m_child_nodes) {
                delete s;
            };
            m_node.m_child_nodes.clear();
        }
        /*
        ┐(P∧Q)<=> ┐P∨┐Q
        ┐(P∨Q)<=> ┐P∧┐Q
        P∨(Q∧R)<=>(P∨Q)∧(P∨R)
        P∧(Q∨R)<=>(P∧Q)∨(P∧R)
        ┐(P→Q)<=> P∧┐Q
        P→Q<=>┐P∨Q
                               top
                               P1

                  A                           B
                  P2

            a1  a2  -a1 -a2              b-1  b0   b1
            Q1  Q2   q1  q2

        yes  P2 → (Q1 ∨ Q2) <=> ┐P2 ∨ (Q1 ∨ Q2) <=> ┐P2 ∨ Q1 ∨ Q2
        sat:  P2 Q1 Q2
              1  1  1
              1  0  1
              1  1  0
              0  x  x

        yes  P2 → (┐q1 ∧ ┐q2) <=> P2 → ┐(q1 ∨ q2) <=> ┐P2 ∨ (┐q1 ∧ ┐q2) <=> ┐P2 ∨ (┐q1 ∧ ┐q2)
        sat:  P2 q1 q2
              1  0  0
              0  x  x
        */
        Vns avoid_asserts(CmprsFork<STATEinterface>& node, Int group) {
            UInt avoid_num = 0;
            UInt target_num = 0;
            for (STATEinterface* sNode : node.child_nodes()) {
                switch (sNode->type()) {
                case Avoid_Node:
                case Survive_Node: avoid_num += 1; break;
                case Fork_Node: {
                    if (sNode->get_fork_node().target_counts(group)) {
                        target_num += 1;
                    }
                    else {
                        avoid_num += 1;
                    }
                    break;
                }
                default: {
                    if ((StateType)group == sNode->type()) target_num += 1;
                }
                };
            }
            if (target_num <= avoid_num) {
                // P2 → (Q1 ∨ Q2)
                if (!target_num) {
                    return Vns(m_ctx.ctx(), 0, 1);
                }
                std::vector<Vns> aasv;
                for (STATEinterface* sNode : node.child_nodes()) {
                    switch (sNode->type()) {
                    case Avoid_Node:
                    case Survive_Node: break;
                    case Fork_Node: {
                        if (sNode->get_fork_node().target_counts(group) == 0)
                            continue;
                        Vns aas_tmp = avoid_asserts(sNode->get_fork_node(), group);
                        Vns top = sNode->get_assert();
                        if (aas_tmp.real()) {
                            aasv.emplace_back(top);
                            continue;
                        }
                        aasv.emplace_back(implies(top, aas_tmp));
                        break;
                    }
                    default: {
                        if ((StateType)group == sNode->type())
                            aasv.emplace_back(sNode->get_assert());
                    }
                    };
                }
                vassert(aasv.size() > 0);
                return logic_or(aasv);
            }
            else {
                // P2 → ┐(q1 ∨ q2)
                if (!avoid_num) {
                    return Vns(m_ctx.ctx(), 0, 1);
                }
                std::vector<Vns> aasv;
                for (STATEinterface* sNode : node.child_nodes()) {
                    switch (sNode->type()) {
                    case Fork_Node: {
                        Vns top = sNode->get_assert();
                        if (sNode->get_fork_node().target_counts(group) == 0) {
                            aasv.emplace_back(top);
                            continue;
                        }
                        Vns aas_tmp = avoid_asserts(sNode->get_fork_node(), group);
                        if (aas_tmp.real()) {
                            continue;
                        }
                        aasv.emplace_back(implies(top, aas_tmp));
                        break;
                    }
                    case Survive_Node:
                    case Avoid_Node: {
                        aasv.emplace_back(sNode->get_assert());
                        break;
                    }
                    default: {
                        if ((StateType)group != sNode->type())
                            aasv.emplace_back(sNode->get_assert());

                        break;
                    }
                    };
                }
                vassert(aasv.size() > 0);
                return !logic_or(aasv);
            }


        }

    private:

        class __struct_cmaps__ {
            STATEinterface* m_node;
            std::hash_map<Addr64, Vns> m_cm;
            UInt m_size;
        public:
            __struct_cmaps__(STATEinterface* node, UInt size) :m_node(node), m_size(size) {
                m_cm.reserve(m_size);
            }

            void add(Addr64 addr, Vns const& m) {
                m_cm[addr] = m;
            }

            operator std::hash_map<Addr64, Vns>& () {
                return m_cm;
            }

            operator STATEinterface* () {
                return m_node;
            }

            bool exist(Addr64 a) {
                return m_cm.lower_bound(a) != m_cm.end();
            }

            void load(std::hash_map<Addr64, GPMana>& cm_ret, std::hash_map<Addr64, bool>& maps) {
                auto it_end = maps.end();
                auto it_start = maps.begin();
                Vns ass = m_node->get_assert();
                for (; it_start != it_end; it_start++) {
                    Addr64 addr = it_start->first;
                    if (exist(addr)) {
                        cm_ret[addr].add(ass, m_cm[addr]);
                    }
                    else {
                        Vns data = m_node->read(addr);
                        cm_ret[addr].add(ass, data);
                    }
                }
            }

            Vns& operator[](UInt idx) {
                return m_cm[idx];
            }

            ~__struct_cmaps__() { }
        };



        void treeCompress(
            std::hash_map<Addr64, GPMana>& cm_ret,/*OUT*/
            CmprsFork<STATEinterface>& node, Int group/*IN*/
        ) {
            std::vector<__struct_cmaps__> changes;
            UInt max = 0;
            for (STATEinterface* sNode : node.child_nodes()) {
                if (sNode->type() >= 0 || (Fork_Node == sNode->type() && sNode->get_fork_node().target_counts(group))) {
                    changes.emplace_back(__struct_cmaps__(sNode, 10));
                    max++;
                }
            }
            changes.reserve(max);

            std::hash_map<Addr64, bool> record;
            for (__struct_cmaps__& changes_node : changes) {
                STATEinterface* sNode = changes_node;
                Vns top = sNode->get_assert();
                if (Fork_Node == sNode->type() && sNode->get_fork_node().target_counts(group)) {
                    sNode->get_write_map(record);
                    std::hash_map<Addr64, GPMana> cm_ret_tmp;
                    treeCompress(cm_ret_tmp, sNode->get_fork_node(), group);
                    auto it_end = cm_ret_tmp.end();
                    auto it_start = cm_ret_tmp.begin();
                    std::hash_map<Addr64, Vns>& fork_cm = changes_node;
                    for (; it_start != it_end; it_start++) {
                        changes_node.add(it_start->first, it_start->second.get());
                        record[it_start->first];
                    }
                }
                if ((StateType)group == sNode->type()) {
                    CmprsTarget<STATEinterface>& target = sNode->get_target_node();
                    sNode->get_write_map(record);
                }
            }

            for (__struct_cmaps__& changes_node : changes) {
                STATEinterface* sNode = changes_node;
                changes_node.load(cm_ret, record);
            }


        }

    };


    using Context32 = CmprsContext<State<Addr32>, State_Tag>;
    using Context64 = CmprsContext<State<Addr64>, State_Tag>;
    using Cmpr32 = Compress<StateCmprsInterface<Addr32>, State<Addr32>, State_Tag>;
    using Cmpr64 = Compress<StateCmprsInterface<Addr64>, State<Addr64>, State_Tag>;
    
};





#endif


