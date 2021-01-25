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
#include "engine/state_base.h"
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

template<typename HWord>
class StateCmprsInterface;


namespace TR {


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



    class StateMEM : public MEM {
        State& m_state;

    public:
        StateMEM(TR::vctx_base &vb, State& state, z3::solver& so, z3::vcontext& ctx, Bool _need_record) :MEM(vb, so, ctx, _need_record), m_state(state) {}
        StateMEM(State& state, z3::solver& so, z3::vcontext& ctx, StateMEM& father_mem, Bool _need_record) :MEM(so, ctx, father_mem, _need_record), m_state(state) {}

        z3::expr idx2Value(Addr64 base, Z3_ast idx) override;
    };






    class State :public StateBase {
        friend class MEM;
        friend class MEM_BASE;
        friend class StateAnalyzer;
        friend class StateCmprsInterface<HWord>;
        using vsize_t = rsval<HWord>;
        using BTS = BTS<State>;
        static constexpr int wide = sizeof(HWord) << 3;

    public:
        vex_context<HWord>& m_vctx;
        //客户机内存 （多线程设置相同user，不同state设置不同user）
        StateMEM          mem;
        EmuEnvironment* m_irvex = nullptr;
        EmuEnvironment& irvex = *m_irvex;

        std::deque<BTS> m_tmp_branch;

        State(TR::vex_context<HWord>& vex_info, HWord gse, Bool _need_record);
        State(State* father_state, HWord gse);
        ~State();
        void start();
        void start(HWord oep) { guest_start = oep; start(); }
        void branchGo();
        //backpoint add
        void hook_add(HWord addr, State_Tag(*_func)(State&), TRControlFlags cflag = CF_None) { m_vctx.hook_add(*this, addr, _func, cflag); }
        vex_context<HWord>& vctx() { return m_vctx; }

        cmpr::CmprsContext<State, State_Tag> cmprContext(HWord target_addr, State_Tag tag) { return cmpr::CmprsContext<State, State_Tag>(m_ctx, target_addr, tag); }
        void compress(cmpr::CmprsContext<State, State_Tag>& ctx);//最大化缩合状态 
        tval tIRExpr(IRExpr*);
        tval CCall(IRCallee* cee, IRExpr** exp_args, IRType ty);
        inline tval ILGop(IRLoadG* lg);

        UInt getStr(std::stringstream& st, HWord addr);
        inline TRsolver& solver() { return solv; }
        inline operator MEM& () { return mem; }
        inline operator Register<REGISTER_LEN>& () { return regs; }
        inline operator z3::context& () const { return const_cast<State*>(this)->m_ctx; }
        

        DirtyCtx getDirtyVexCtx();
        tval dirty_call(IRCallee* cee, IRExpr** exp_args, IRType ty);
        tval dirty_call(const HChar* name, void* func, std::initializer_list<rsval<Addr64>> parms, IRType ty);
        HWord getGSPTR() { return dirty_get_gsptr<HWord>(getDirtyVexCtx()); }

        void vex_push(const rsval<HWord>& v);
        template<typename T, TASSERT(std::is_arithmetic<T>::value)>
        void vex_push(T v) { vex_push(rsval<HWord>(m_ctx, v)); }

        rsval<HWord> vex_pop();
        //sp[n*size_t]
        rsval<HWord> vex_stack_get(int n);

        //interface :

        virtual MEM_BASE& membase() override { return mem; };
        virtual inline void traceStart() { return; };
        virtual inline void traceFinish() { return; };
        virtual inline void traceIRSB(IRSB*) { return; };
        virtual inline void traceIrsbEnd(IRSB*) { return; };
        virtual inline void traceIRStmtEnd(IRStmt*) { return; };
        virtual inline void traceInvoke(HWord call, HWord bp) { return; };

        StateBase* mkState(HWord ges) { return ForkState(ges); }
        virtual rsval<HWord> TEB() { VPANIC("need to implement the method"); }
        virtual StateBase* ForkState(HWord ges) override { VPANIC("need to implement the method"); return nullptr; }
    private:
        virtual State_Tag Ijk_call(IRJumpKind) { VPANIC("need to implement the method"); m_status = Death; };
        virtual void  cpu_exception(Expt::ExceptionBase const& e) { VPANIC("need to implement the method"); m_status = Death; }
        virtual bool  StateCompression(State const& next) { return true; }
        virtual void  StateCompressMkSymbol(State const& newState) {  };
        //State::delta maybe changed by callback
        virtual State_Tag call_back_hook(Hook_struct const& hs) {
            State_Tag(*CB) (State&) = (State_Tag(*) (State&))hs.cb;
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



template<typename HWord>
static inline std::ostream& operator<<(std::ostream& out, const TR::State & n) {
    return out << (std::string)n;
}

template<typename HWord>
inline std::ostream& operator << (std::ostream& out, const TR::InvocationStack<HWord>& e) {
    return out << (std::string)e; 
}

#endif

