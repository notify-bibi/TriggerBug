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

#ifndef _STATE_CLASS_DEFS_
#define _STATE_CLASS_DEFS_

#include "engine/engine.h"
#include "engine/basic_var.hpp"
#include "engine/vex_context.h"
#include "engine/register.h"
#include "engine/memory.h"
#include "engine/kernel.h"
#include "engine/ir_dirty.h"
#include "engine/compress.h"
#include "engine/emu_environment.h"
#include "z3_target_call/z3_target_call.h"
#include <deque>



namespace cmpr {
    using Context32 = CmprsContext<TR::State<Addr32>, TR::State_Tag>;
    using Context64 = CmprsContext<TR::State<Addr64>, TR::State_Tag>;
};

extern void* funcDict(void*);
extern void Func_Map_Init();
extern int eval_all(std::deque<tval>& result, z3::solver& solv, Z3_ast bv);
//-1 err. 0 false. 1 true. 2 false || true.
int eval_all_bool(z3::solver& solv, Z3_ast nia);
extern std::string replace(const char* pszSrc, const char* pszOld, const char* pszNew);
extern UInt arch_2_stack_sp_iroffset(VexArch arch);


namespace cmpr {
    template<class CompressClass, typename StateStatus>
    class CmprsContext;

    template<class STATEinterface, class CompressClass, typename StateStatus>
    class Compress;

}

template<typename THword>
class StateCmprsInterface;

template<typename THword>
class StateAnalyzer;

namespace TR {

    class TRsolver :public z3::solver {
        template<typename THword>
        friend class State;
        friend class BranchChunk;
        friend class StateX86;
        friend class StateAMD64;
        bool                    m_solver_snapshot = false;//if solver::push() m_solver_snapshot = true
        std::vector<sbool>        m_asserts;
    public:
        TRsolver(z3::context& c);
        TRsolver(z3::context& c, solver const& src, translate x) : z3::solver(c, src, x) { m_asserts.reserve(2); }
        void push() { m_solver_snapshot = true; z3::solver::push(); }
        void pop() { z3::solver::pop(); m_solver_snapshot = false; }
        bool is_snapshot() { return m_solver_snapshot; }

        std::vector<sbool> const& get_asserts() const { return m_asserts; };

        //不会保存assert到solver,因为在push之前会进行push
        void add(sbool const& e);

        void add(rsbool const& e) { add(e.tos()); }

        void check_if_forget_pop();

        void add_assert(const sbool& assert);

        inline operator Z3_context() { return ctx(); }

        static z3::solver mk_tactic_solver_default(z3::context& c);

        void use_tactic(z3::tactic& t) {
            *(z3::solver*)(this) = t.mk_solver();
        }
    private:
    };

    //Functional programming
    template<typename THword>
    class InvocationStack {
        std::deque<THword> guest_call_stack;
        std::deque<THword> guest_stack;
    public:
        inline InvocationStack() {}
        inline InvocationStack(InvocationStack<THword> const& fsk) {
            guest_call_stack = fsk.guest_call_stack;
            guest_stack = fsk.guest_stack;
        }
        inline void push(THword call_ptr, THword bp/*栈底*/) {
            guest_call_stack.push_back(call_ptr);
            guest_stack.push_back(bp);
        }
        inline void pop() {
            if (!guest_call_stack.empty()) {
                guest_call_stack.pop_back();
                guest_stack.pop_back();
            }
        }
        template<typename THword> friend bool operator==(InvocationStack<THword> const& a, InvocationStack<THword> const& b);
        void operator=(InvocationStack<THword> const& b) {
            guest_call_stack = b.guest_call_stack;
            guest_stack = b.guest_stack;
        }

        void clear() { guest_call_stack.clear(); guest_stack.clear(); }
        bool empty() const { return guest_call_stack.empty(); }
        UInt size() const { return guest_call_stack.size(); }
        operator std::string() const;
    };


    template<typename THword>
    inline bool operator==(InvocationStack<THword> const& a, InvocationStack<THword> const& b) {
        return (a.guest_call_stack == b.guest_call_stack) && (a.guest_stack == b.guest_stack);
    }

    //branch_temp_state
    template<class STATE>
    class BTS {
        STATE& m_state;
        Addr64 m_oep;
        rsbool m_guard;
        rsbool m_addr_eq;
        STATE* m_child_state = nullptr;
        IRJumpKind m_jump_kd = Ijk_Boring;
    public:
        inline BTS(STATE& s, Addr64 start, rsbool& guard) :
            m_state(s), m_oep(start), m_guard(guard), m_addr_eq(guard.ctx(), false)
        { };

        inline BTS(STATE& s, Addr64 start, rsbool&& guard) :
            m_state(s), m_oep(start), m_guard(guard), m_addr_eq(guard.ctx(), false)
        { };

        inline BTS(STATE& s, Addr64 start, rsbool& guard, rsbool& addr_eq) :
            m_state(s), m_oep(start), m_guard(guard), m_addr_eq(addr_eq) 
        { };

        inline BTS(STATE& s, Addr64 start, rsbool&& guard, rsbool& addr_eq) :
            m_state(s), m_oep(start), m_guard(guard), m_addr_eq(addr_eq)
        { };

        inline BTS(STATE& s, Addr64 start, rsbool&& guard, rsbool&& addr_eq) :
            m_state(s), m_oep(start), m_guard(guard), m_addr_eq(addr_eq)
        { };

        inline IRJumpKind jump_kd() const { return m_jump_kd; }
        inline void set_jump_kd(IRJumpKind kd) { m_jump_kd = kd; }

        virtual STATE* child() {
            if (m_child_state)
                return m_child_state;

            m_child_state = (STATE*)m_state.mkState(m_oep);
            m_child_state->set_jump_kd(m_jump_kd);
            m_child_state->solver().add_assert(m_guard.tos());
            if (m_addr_eq.symb()) {
                m_child_state->solver().add_assert(m_addr_eq.tos());
            }
            return m_child_state;
        }

        Addr64 get_oep() { return m_oep; }
        const sbool& get_guard() const { return m_guard; }
        ~BTS(){}

        BTS(const BTS& a) : m_state(a.m_state), m_oep(a.m_oep), m_guard(a.m_guard), m_addr_eq(a.m_addr_eq), m_child_state(a.m_child_state) {};
        
        void operator = (const BTS& a) { this->BTS::~BTS(); this->BTS::BTS(a); }
    };


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
            Iterator(const _Chunk* s) :m_ptr(s), m_fd(s->m_fd) {
            }

            inline bool operator!=(const Iterator& src)
            {
                return m_ptr != src.m_ptr;
            }

            inline void operator++()
            {
                m_ptr = m_fd;
                m_fd = m_fd->m_fd;
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




    template<typename THword>
    class StateMEM : public MEM<THword> {
        State<THword>& m_state;

    public:
        StateMEM(TR::vctx_base &vb, State<THword>& state, z3::solver& so, z3::vcontext& ctx, Bool _need_record) :MEM<THword>(vb, so, ctx, _need_record), m_state(state) {}
        StateMEM(State<THword>& state, z3::solver& so, z3::vcontext& ctx, StateMEM& father_mem, Bool _need_record) :MEM<THword>(so, ctx, father_mem, _need_record), m_state(state) {}

        z3::expr idx2Value(Addr64 base, Z3_ast idx) override;
    };






    template<typename THword>
    class State :public Kernel {
        friend class MEM<THword>;
        friend class StateAnalyzer<THword>;
        friend class StateCmprsInterface<THword>;
        using vsize_t = rsval<THword>;
        using VexIRTemp = EmuEnvironment;
        using BTS = BTS<State<THword>>;
        static constexpr int wide = sizeof(THword) << 3;

    public:
        vex_context<THword>& m_vctx;
    private:
        //当前state的入口点
        THword        guest_start_ep;
        //客户机state的eip（计数器eip）
        THword        guest_start;
    private:
        bool        m_dirty_vex_mode = false;
        DirtyCtx    m_dctx = nullptr;
        VexArchInfo* vai_guest, * vai_host;

        Bool        need_record;
        UInt        m_z3_bv_const_n;
        std::mutex  m_state_lock;
        THword        m_delta;
        State_Tag   m_status;
        IRJumpKind  m_jump_kd;
    public:
        InvocationStack<THword>   m_InvokStack;
        TRsolver                solv;
        //客户机寄存器
        Register<REGISTER_LEN>  regs;
        //客户机内存 （多线程设置相同user，不同state设置不同user）
        StateMEM<THword>          mem;
        VexIRTemp                  irvex;
        BranchManager<State<THword>> branch;
        std::deque<BTS> m_tmp_branch;

        State(TR::vex_context<THword>& vex_info, THword gse, Bool _need_record);
        State(State* father_state, THword gse);
        void read_mem_dump(const char*);
    public:
        ~State();
        void start();
        void start(THword oep) { guest_start = oep; start(); }
        void branchGo();
        //ip = ip + offset
        inline void set_delta(THword offset) { m_delta = offset; };
        inline void goto_ptr(THword addr) { m_delta = addr - guest_start; };
        //backpoint add
        void hook_add(THword addr, State_Tag(*_func)(State<THword>&), TRControlFlags cflag = CF_None) { m_vctx.hook_add(*this, addr, _func, cflag); }
        vex_context<THword>& vctx() { return m_vctx; }

        cmpr::CmprsContext<State<THword>, State_Tag> cmprContext(THword target_addr, State_Tag tag) { return cmpr::CmprsContext<State<THword>, State_Tag>(m_ctx, target_addr, tag); }
        void compress(cmpr::CmprsContext<State<THword>, State_Tag>& ctx);//最大化缩合状态 
        tval tIRExpr(IRExpr*);
        tval CCall(IRCallee* cee, IRExpr** exp_args, IRType ty);
        inline tval ILGop(IRLoadG* lg);

        tval mk_int_const(UShort nbit);
        tval mk_int_const(UShort n, UShort nbit);
        UInt getStr(std::stringstream& st, THword addr);
        inline TRsolver& solver() { return solv; }
        inline operator MEM<THword>& () { return mem; }
        inline operator Register<REGISTER_LEN>& () { return regs; }
        inline operator z3::context& () const { return const_cast<State<THword>*>(this)->m_ctx; }
        
        Addr64 get_cpu_ip() override { return guest_start; }
        inline THword get_state_ep() { return guest_start_ep; }
        inline State_Tag status() { return m_status; }
        inline void set_status(State_Tag t) { m_status = t; };
        inline IRJumpKind jump_kd() const { return m_jump_kd; }
        inline void set_jump_kd(IRJumpKind kd) { m_jump_kd = kd; }
        operator std::string() const;

        DirtyCtx getDirtyVexCtx();
        tval dirty_call(IRCallee* cee, IRExpr** exp_args, IRType ty);
        tval dirty_call(const HChar* name, void* func, std::initializer_list<rsval<Addr64>> parms, IRType ty);
        HWord getGSPTR() { return dirty_get_gsptr<THword>(getDirtyVexCtx()); }

        void vex_push(const rsval<THword>& v);
        template<typename T, TASSERT(std::is_arithmetic<T>::value)>
        void vex_push(T v) { vex_push(rsval<THword>(m_ctx, v)); }

        rsval<THword> vex_pop();
        //sp[n*size_t]
        rsval<THword> vex_stack_get(int n);

        //interface :

        virtual inline void traceStart() { return; };
        virtual inline void traceFinish() { return; };
        virtual inline void traceIRSB(IRSB*) { return; };
        virtual inline void traceIrsbEnd(IRSB*) { return; };
        virtual inline void traceIRStmtEnd(IRStmt*) { return; };
        virtual inline void traceInvoke(THword call, THword bp) { return; };

        Kernel* mkState(THword ges) { return ForkState(ges); }
        virtual rsval<THword> TEB() { VPANIC("need to implement the method"); }
        virtual Kernel* ForkState(THword ges) { VPANIC("need to implement the method"); return nullptr; }
    private:
        virtual State_Tag Ijk_call(IRJumpKind) { VPANIC("need to implement the method"); m_status = Death; };
        virtual void  cpu_exception(Expt::ExceptionBase const& e) { VPANIC("need to implement the method"); m_status = Death; }
        virtual bool  StateCompression(State const& next) { return true; }
        virtual void  StateCompressMkSymbol(State const& newState) {  };
        //State::delta maybe changed by callback
        virtual State_Tag call_back_hook(Hook_struct const& hs) {
            State_Tag(*CB) (State<THword>&) = (State_Tag(*) (State<THword>&))hs.cb;
            return (CB) ? (CB)(*this) : Running;
        }
        State_Tag _call_back_hook(Hook_struct const& hs) {
            State_Tag ret = call_back_hook(hs);
            solv.check_if_forget_pop();
            return ret;
        }



        bool vex_start();
    };


};



template<typename THword>
static inline std::ostream& operator<<(std::ostream& out, const TR::State<THword> & n) {
    return out << (std::string)n;
}

template<typename THword>
inline std::ostream& operator << (std::ostream& out, const TR::InvocationStack<THword>& e) {
    return out << (std::string)e; 
}

#endif

