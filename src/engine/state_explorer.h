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
//#include "engine/compress.h"
#include "engine/emu_environment.h"
#include "z3_target_call/z3_target_call.h"
#include <deque>



namespace cmpr {
    //using Context = CmprsContext<TR::StateBase, TR::State_Tag>;
};

extern void* funcDict(void*);
extern void Func_Map_Init();
extern int eval_all(std::deque<sv::tval>& result, z3::solver& solv, Z3_ast bv);
//-1 err. 0 false. 1 true. 2 false || true.
int eval_all_bool(z3::solver& solv, Z3_ast nia);
extern std::string replace(const char* pszSrc, const char* pszOld, const char* pszNew);



namespace cmpr {
    template<class CompressClass, typename StateStatus>
    class CmprsContext;

    template<class STATEinterface, class CompressClass, typename StateStatus>
    class Compress;

}

class StateCmprsInterface;
class VexIRDirty;

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

            m_child_state = (STATE*)m_state.ForkState(m_oep);
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


    enum Vex_Kind
    {
        vUpdate, // 
        vFork,
        vStop,
    };


    // i'm just a cpu hardware
    class State : public StateBase {
        friend class StateAnalyzer;
        friend class StateCmprsInterface;
        friend class VexIRDirty;
        using vsize_t = rsval<HWord>;
        using BTSType = BTS<State>;

        bool                   m_call_stack_is_empty = false;
        std::mutex             m_state_lock;
        InvocationStack<HWord> m_InvokStack;
        EmuEnvironment        *m_irvex;
        TRControlFlags         m_trtraceflags;
        DirtyCtx               m_dctx = nullptr;
        Bool                   m_is_dirty_mode; // vex状态
    public:

        State(vex_context& vctx, VexArch guest_arch);
        State(State& father, HWord gse);

        ~State();
        // x96
        void x86_set_mode(UChar cs);

        // -------------   dirty  -------------

        DirtyCtx getDirtyVexCtx();
        sv::tval dirty_call(const IRCallee* cee, IRExpr** const exp_args, IRType ty);
        sv::tval dirty_call(const HChar* name, void* func, std::initializer_list<rsval<Addr64>> parms, IRType ty);
        HWord getGSPTR();


        template<int ea_nbits> 
        sv::tval tIRCallee(const IRCallee* cee, IRExpr** const exp_args, IRType ty);
        sv::tval tCCall(const IRCallee* cee, IRExpr** const exp_args, IRType ty);

        // ------------- dirty end -------------

        sv::tval ILGop(const IRLoadG* lg);
        void do_Ijk_Ret();
        template<int ea_nbits>
        void do_Ijk_Call(const IRExpr* irsb_next);
        sv::tval tIRExpr(const IRExpr*);
        template<int ea_nbits> void tIRStmt(const IRTypeEnv* tyenv, const IRStmt *s);

        template<int ea_nbits>
        Vex_Kind emu_irsb_next(std::deque<BTSType>& tmp_branch, HWord& guest_start, IRJumpKind jumpkind, const IRExpr* next);

        template<int ea_nbits>
        Vex_Kind emu_irsb(std::deque<BTSType>& tmp_branch, HWord& guest_start, State_Tag& status, const IRSB* irsb);


        bool vex_main_loop(IRSB*& irsb, HWord& guest_start, Addr avoid);
        void start(); // guest emu
        void start(HWord ep); // guest emu
        void start(HWord& guest_start, EmuEnvironment*, Addr avoid); // guest or host emu
    private:
        void v_start(HWord& guest_start, Addr avoid); // emu

        void set_dirty_mode() { m_is_dirty_mode = true; }
        void clean_dirty_mode() { m_is_dirty_mode = false; }
        bool is_dirty_mode() { return m_is_dirty_mode; }
    public:
        void dirty_call_run(IRTemp tmp, IRType tmpType, const IRDirty* dirty);

        void branchGo();
        //backpoint add
        //void hook_add(HWord addr, State_Tag(*_func)(StateBase&), TRControlFlags cflag = CF_None) { /*m_vctx.hook_add(m_state, addr, _func, cflag);*/ }
        

        //cmpr::CmprsContext<StateBase, State_Tag> cmprContext(HWord target_addr, State_Tag tag) { return cmpr::CmprsContext<State, State_Tag>(m_ctx, target_addr, tag); }
        //最大化缩合状态 
        void compress(cmpr::CmprsContext<StateBase, State_Tag>& ctx);

        inline EmuEnvironment& irvex() { return *m_irvex; }
        void set_irvex(EmuEnvironment* e);


        inline InvocationStack<HWord>& get_InvokStack() { return m_InvokStack; }



        // ---------------------   stack  ---------------------
        template<typename T, TASSERT(std::is_arithmetic<T>::value)>
        void vex_push_const(T v) {
            vex_push<T>(rsval<T>(m_ctx, v));
        }
        template<typename THword> void vex_push(const rsval<THword>& v);
        template<typename THword> rsval<THword> vex_pop();
        //sp[n*size_t]
        template<typename THword> rsval<THword> vex_stack_get(int n);
        // --------------------- stack end ---------------------

    public:
        virtual bool  StateCompression(State const& next) { return true; }
        virtual void  StateCompressMkSymbol(State const& newState) {  };
        //State::delta maybe changed by callback
        virtual State_Tag call_back_hook(Hook_struct const& hs) {
            /*State_Tag(*CB) (State&) = (State_Tag(*) (StateBase&))hs.cb;
            return (CB) ? (CB)(*this) : Running;*/
        }

        State_Tag _call_back_hook(Hook_struct const& hs) {
            State_Tag ret = call_back_hook(hs);
            solv.check_if_forget_pop();
            return ret;
        }
        // interface
        virtual StateBase* ForkState(HWord ges) override { return new State(*this, ges); }
        virtual State_Tag Ijk_call(IRJumpKind jk);
        virtual void cpu_exception(Expt::ExceptionBase const& e);
        virtual void avoid_anti_debugging();
    public:
        void clean();//清空多余的指针对象（m_dctx）
        inline TR::TRControlFlags setFlag(TR::TRControlFlags t) { return (TR::TRControlFlags)setFlag((ULong)t); }
        inline ULong setFlag(ULong f) { return *(ULong*)&m_trtraceflags |= f; }

        inline TR::TRControlFlags delFlag(TR::TRControlFlags f) { return (TR::TRControlFlags)delFlag((ULong)f); }
        inline ULong delFlag(ULong f) { return *(ULong*)&m_trtraceflags &= ~f; }

        inline bool getFlag(TR::TRControlFlags t) const { return m_trtraceflags & t; }
        inline ULong getFlags() const { return m_trtraceflags; }
        inline void setFlags(TR::TRControlFlags t) { m_trtraceflags = t; };
        //inline ULong& getFlagRef() { return m_trtraceflags; }


        void pp_call_space();
        void pp_call_space(HWord addr);

    public:
        // interface

        virtual void traceStart(HWord ea);
        virtual void traceFinish(HWord ea);
        virtual void traceIRSB(HWord ea, const IRSB*);;
        virtual void traceIrsbEnd(const IRSB*);
        virtual void traceIRStmtStart(const IRStmt*);
        virtual void traceIRStmtEnd(const IRStmt*);
        virtual void traceInvoke(HWord call, HWord bp);

    };












};


extern unsigned currentThreadId();

namespace SP {
    //class SExplore : public TR::SExplore {


    //    SExplore(TR::vex_context& vctx, TR::StateBase& base) : TR::SExplore(vctx, base), m_trtraceflags(TR::CF_None) {};


    //    

    //};
};


#endif

