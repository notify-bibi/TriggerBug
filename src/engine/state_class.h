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
#include "engine/vex_context.h"
#include "engine/variable.h"
#include "engine/register.h"
#include "engine/memory.h"
#include "engine/kernel.h"
#include "engine/ir_dirty.h"
#include "engine/compress.h"
#include "engine/emu_environment.h"
#include "z3_target_call/z3_target_call.h"
#include "crypto_analyzer/crypto_analyzer.h"
#include <deque>


extern void* funcDict(void*);
extern void Func_Map_Init();
extern int eval_all(std::vector<Vns>& result, z3::solver& solv, Z3_ast nia);
extern std::string replace(const char* pszSrc, const char* pszOld, const char* pszNew);
extern UInt arch_2_stack_sp_iroffset(VexArch arch);


namespace cmpr {
    template<class CompressClass, typename StateStatus>
    class CmprsContext;

    template<class STATEinterface, class CompressClass, typename StateStatus>
    class Compress;

}

template<typename ADDR>
class StateCmprsInterface;

namespace TR {

    class TRsolver :public z3::solver {
        template<typename ADDR>
        friend class State;
        friend class BranchChunk;
        friend class StateX86;
        friend class StateAMD64;
        bool                    m_solver_snapshot = false;//if solver::push() m_solver_snapshot = true
        std::vector<Vns>        m_asserts;
    public:
        TRsolver(z3::context& c) :
            z3::solver(mk_tactic_solver_default(c))
            /*z3::solver(c)*/
        {
            m_asserts.reserve(2);
        };
        TRsolver(z3::context& c, solver const& src, translate x) : z3::solver(c, src, x) { m_asserts.reserve(2); }
        void push() { m_solver_snapshot = true; z3::solver::push(); }
        void pop() { z3::solver::pop(); m_solver_snapshot = false; }
        bool is_snapshot() { return m_solver_snapshot; }
        std::vector<Vns> const& get_asserts() const { return m_asserts; };
        //不会保存assert到solver,因为在push之前会进行push
        void add(z3::expr const& e) {
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
        void add_assert(z3::expr const& assert, Bool ToF) { add_assert(assert, ToF); }
        inline void add_assert(z3::expr const& assert) { add_assert(assert, True); };
        inline void add_assert_eq(z3::expr const& eqA, z3::expr const& eqB) { add_assert_eq(Vns(eqA.ctx(), (Z3_ast)eqA), Vns(eqB.ctx(), (Z3_ast)eqB)); }
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
        void use_tactic(z3::tactic& t) {
            *(z3::solver*)(this) = t.mk_solver();
        }
    private:
    };

    //Functional programming
    template<typename ADDR>
    class InvocationStack {
        std::deque<ADDR> guest_call_stack;
        std::deque<ADDR> guest_stack;
    public:
        inline InvocationStack() {}
        inline InvocationStack(InvocationStack<ADDR> const& fsk) {
            guest_call_stack = fsk.guest_call_stack;
            guest_stack = fsk.guest_stack;
        }
        inline void push(ADDR call_ptr, ADDR bp/*栈底*/) {
            guest_call_stack.push_back(call_ptr);
            guest_stack.push_back(bp);
        }
        inline void pop() {
            if (!guest_call_stack.empty()) {
                guest_call_stack.pop_back();
                guest_stack.pop_back();
            }
        }
        template<typename ADDR> friend bool operator==(InvocationStack<ADDR> const& a, InvocationStack<ADDR> const& b);
        void operator=(InvocationStack<ADDR> const& b) {
            guest_call_stack = b.guest_call_stack;
            guest_stack = b.guest_stack;
        }

        void clear() { guest_call_stack.clear(); guest_stack.clear(); }
        bool empty() const { return guest_call_stack.empty(); }
        UInt size() const { return guest_call_stack.size(); }
        operator std::string() const;
    };

    template<typename ADDR>
    inline bool operator==(InvocationStack<ADDR> const& a, InvocationStack<ADDR> const& b) {
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


    template<typename ADDR>
    class StateAnalyzer;




    template<typename ADDR>
    class StateMEM : public MEM<ADDR> {
        State<ADDR>& m_state;

    public:
        StateMEM(TR::vctx_base &vb, State<ADDR>& state, z3::solver& so, z3::vcontext& ctx, Bool _need_record) :MEM(vb, so, ctx, _need_record), m_state(state) {}
        StateMEM(State<ADDR>& state, z3::solver& so, z3::vcontext& ctx, StateMEM& father_mem, Bool _need_record) :MEM(so, ctx, father_mem, _need_record), m_state(state) {}

        z3::expr idx2Value(Addr64 base, Z3_ast idx) override;
    };






    template<typename ADDR>
    class State :public Kernel {
        friend class MEM<ADDR>;
        friend class StateAnalyzer<ADDR>;
        friend class StateCmprsInterface<ADDR>;

    public:
        vex_context<ADDR>& m_vctx;
    private:
        //当前state的入口点
        ADDR        guest_start_ep;
        //客户机state的eip（计数器eip）
        ADDR        guest_start;
    private:
        bool        m_dirty_vex_mode = false;
        DirtyCtx    m_dctx = nullptr;
        VexArchInfo* vai_guest, * vai_host;

        Bool        need_record;
        UInt        m_z3_bv_const_n;
        std::mutex  m_state_lock;
        ADDR        m_delta;
        State_Tag   m_status;
    public:
        Vns* m_ir_temp = nullptr;
        InvocationStack<ADDR>   m_InvokStack;
        TRsolver                solv;
        //客户机寄存器
        Register<REGISTER_LEN>  regs;
        //客户机内存 （多线程设置相同user，不同state设置不同user）
        StateMEM<ADDR>          mem;
        BranchManager<State<ADDR>> branch;

        State(TR::vex_context<ADDR>& vex_info, ADDR gse, Bool _need_record);
        State(State* father_state, ADDR gse);
        void read_mem_dump(const char*);

        ~State();
        inline void setTemp(Vns* t) { m_ir_temp = t; }
        void start();
        void start(ADDR oep) { guest_start = oep; start(); }
        void branchGo();
        //ip = ip + offset
        inline void set_delta(ADDR offset) { m_delta = offset; };
        inline void goto_ptr(ADDR addr) { m_delta = addr - guest_start; };
        //backpoint add
        void hook_add(ADDR addr, State_Tag(*_func)(State<ADDR>&), TRControlFlags cflag = CF_None) { m_vctx.hook_add(*this, addr, _func, cflag); }

        cmpr::CmprsContext<State<ADDR>, State_Tag> cmprContext(ADDR target_addr, State_Tag tag) { return cmpr::CmprsContext<State<ADDR>, State_Tag>(m_ctx, target_addr, tag); }
        void compress(cmpr::CmprsContext<State<ADDR>, State_Tag>& ctx);//最大化缩合状态 
        inline Vns tIRExpr(IRExpr*);
        Vns CCall(IRCallee* cee, IRExpr** exp_args, IRType ty);
        inline Vns ILGop(IRLoadG* lg);

        Vns mk_int_const(UShort nbit);
        Vns mk_int_const(UShort n, UShort nbit);
        UInt getStr(std::stringstream& st, ADDR addr);
        inline operator MEM<ADDR>& () { return mem; }
        inline operator Register<REGISTER_LEN>& () { return regs; }
        inline operator z3::context& () const { return const_cast<State<ADDR>*>(this)->m_ctx; }
        
        Addr64 get_cpu_ip() override { return guest_start; }
        inline ADDR get_state_ep() { return guest_start_ep; }
        inline State_Tag status() { return m_status; }
        inline void set_status(State_Tag t) { m_status = t; };
        operator std::string() const;

        DirtyCtx getDirtyVexCtx();
        Vns dirty_call(IRCallee* cee, IRExpr** exp_args, IRType ty);
        Vns dirty_call(const HChar* name, void* func, std::initializer_list<Vns> parms, IRType ty);
        Addr64 getGSPTR() { return dirty_get_gsptr<ADDR>(getDirtyVexCtx()); }

        template<typename T>
        void vex_push(T v) {
            Vns sp = regs.Iex_Get<(IRType)(sizeof(ADDR) << 3)>(m_vctx.gRegsSpOffset()) - sizeof(ADDR);
            regs.Ist_Put(m_vctx.gRegsSpOffset(), sp);
            mem.Ist_Store(sp, (ADDR)v);
        }

        template<>
        void vex_push(Vns const& v) {
            Vns sp = regs.Iex_Get<(IRType)(sizeof(ADDR)<<3)>(m_vctx.gRegsSpOffset()) - sizeof(ADDR);
            regs.Ist_Put(m_vctx.gRegsSpOffset(), sp);
            mem.Ist_Store(sp, v);
        }

        Vns vex_pop();
        //sp[n*size_t]
        Vns vex_stack_get(Int n);

        //interface :

        virtual inline void traceStart() { return; };
        virtual inline void traceFinish() { return; };
        virtual inline void traceIRSB(IRSB*) { return; };
        virtual inline void traceIrsbEnd(IRSB*) { return; };
        virtual inline void traceIRStmtEnd(IRStmt*) { return; };
        virtual inline void traceInvoke(ADDR call, ADDR bp) { return; };

        Kernel* mkState(ADDR ges) { return ForkState(ges); }
        virtual Vns TEB() { VPANIC("need to implement the method"); return Vns(); }
        virtual Kernel* ForkState(ADDR ges) { VPANIC("need to implement the method"); return nullptr; }
    private:
        virtual State_Tag Ijk_call(IRJumpKind) { VPANIC("need to implement the method"); m_status = Death; };
        virtual void  cpu_exception(Expt::ExceptionBase const& e) { VPANIC("need to implement the method"); m_status = Death; }
        virtual bool  StateCompression(State const& next) { return true; }
        virtual void  StateCompressMkSymbol(State const& newState) {  };
        //State::delta maybe changed by callback
        virtual State_Tag call_back_hook(Hook_struct const& hs) {
            State_Tag(*CB) (State<ADDR>&) = (State_Tag(*) (State<ADDR>&))hs.cb;
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



template<typename ADDR>
static inline std::ostream& operator<<(std::ostream& out, const TR::State<ADDR> & n) {
    return out << (std::string)n;
}

template<typename ADDR>
inline std::ostream& operator << (std::ostream& out, const TR::InvocationStack<ADDR>& e) {
    return out << (std::string)e; 
}

#endif

