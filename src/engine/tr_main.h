
/* ---------------------------------------------------------------------------------------
 *      Hex-Rays Decompiler project
 *      Copyright (c) 2019 Microsoft Corporation by notify-bibi@github, 2496424084@qq.com
 *      ALL RIGHTS RESERVED.
 *
 *      这是 TR::State<BitWide> 的派生类定义地，只允许 32 or 64 
 *
 * ---------------------------------------------------------------------------------------
 */


#ifndef _TRIGGERBUG_
#define _TRIGGERBUG_

#include "engine.h"
#include "engine/variable.h"
#include "engine/register.h"
#include "engine/memory.h"
#include "engine/state_class.h"
#include "engine/state_analyzer.h"
#include "engine/guest_helper_defs.h"


unsigned currentThreadId();

namespace SP {
    template <typename ADDR, class TC>
    class StatePrinter;
};

namespace TR {

    class StateX86 : public State<Addr32> {
        friend class SP::StatePrinter<Addr32, StateX86>;
        friend class win32;
        friend class linux32;
        StateX86(StateX86* father_state, Addr32 gse) :State(father_state, gse) {};
    public:
        StateX86(vex_context<Addr32>& vex_info, Addr32 gse, Bool _need_record) :State(vex_info, gse, _need_record) 
        {  };

        virtual StateBase* ForkState(HWord ges) override { return new StateX86(this, ges); };
        virtual bool  StateCompression(State<Addr32> const& next) override { return true; }
        virtual void  StateCompressMkSymbol(State<Addr32> const& newState) override {  };
        //Thread Environment Block
        rsval<Addr32> TEB() override;
    };





    class StateAMD64 : public State<Addr64> {
        friend class SP::StatePrinter<Addr64, StateAMD64>;
        friend class win64;
        friend class linux64;
        StateAMD64(StateAMD64* father_state, Addr64 gse) :
            State(father_state, gse)
        {
        };
    public:
        StateAMD64(vex_context<Addr64>& vex_info, Addr64 gse, Bool _need_record) :
            State(vex_info, gse, _need_record)
        {};


        virtual StateBase* ForkState(Addr64 ges) override { return new StateAMD64(this, ges); };
        virtual bool  StateCompression(State<Addr64> const& next) override { return true; }
        virtual void  StateCompressMkSymbol(State<Addr64> const& newState) override {  };
        //Thread Environment Block
        rsval<Addr64> TEB() override { return regs.get<Ity_I64>(AMD64_IR_OFFSET::FS_CONST); }
    };


};

namespace SP {

    template <typename ADDR, class TC>
    class StatePrinter : public TC {
        TR::TRControlFlags m_trtraceflags;
    public:
        StatePrinter(StatePrinter* father_state, ADDR gse) : TC(father_state, gse), m_trtraceflags(father_state->m_trtraceflags) {};

        inline TR::TRControlFlags setFlag(TR::TRControlFlags t) { return (TR::TRControlFlags)setFlag((ULong)t); }
        inline ULong setFlag(ULong f) { return *(ULong*)&m_trtraceflags |= f; }

        inline TR::TRControlFlags delFlag(TR::TRControlFlags f) { return (TR::TRControlFlags)delFlag((ULong)f); }
        inline ULong delFlag(ULong f) { return *(ULong*)&m_trtraceflags &= ~f; }

        inline bool getFlag(TR::TRControlFlags t) const { return m_trtraceflags & t; }
        inline ULong getFlags() const { return m_trtraceflags; }
        inline ULong& getFlagRef() { return m_trtraceflags; }

        void pp_call_space(){
            UInt size = TC::get_InvokStack().size();
            printf("[%-2d:%2d]", size, TC::mem.get_user());
            for (UInt i = 0; i < size; i++) {
                vex_printf("  ");
            }
        }
        void pp_call_space(ADDR addr) {
            UInt size = TC::get_InvokStack().size();
            printf("[%-2d:%2d] 0x%-16x", size, TC::mem.get_user(), addr);
            for (UInt i = 0; i < size; i++) {
                vex_printf("  ");
            }
        }
    public:
        StatePrinter(TR::vex_context<ADDR>& vex_info, ADDR gse, Bool _need_record) :
            TC(vex_info, gse, _need_record),
            m_trtraceflags(CF_None) {};


        void   traceStart() override {
            if (getFlag(CF_traceState)) {
                pp_call_space();
                std::cout << "\n+++++++++++++++ Thread ID: " << currentThreadId() << "  address: " << std::hex << TC::get_cpu_ip() << "  Started +++++++++++++++\n" << std::endl;
            };
        }

        void   traceFinish() override {
            if (getFlag(CF_traceState)) {
                if (TC::status() == Fork) {
                    vex_printf("Fork from: %p to:{ ", TC::get_cpu_ip());
                    for (auto bc : TC::branch) {
                        vex_printf(" %p", bc->get_state_ep());
                    }
                    vex_printf(" };", TC::get_cpu_ip());
                }
                std::cout << "\n+++++++++++++++ Thread ID: " << currentThreadId() << "  address: " << std::hex << TC::get_cpu_ip() << "  OVER +++++++++++++++\n" << std::endl;
            }
        }

        void   traceIRStmtEnd(IRStmt* s) override {
            if (getFlag(CF_ppStmts)) {
                pp_call_space();
                if (s->tag == Ist_WrTmp) {
                    UInt tmp = s->Ist.WrTmp.tmp;
                    vex_printf("t%u = ", tmp);
                    std::cout << TC::irvex[tmp];
                    vex_printf(" = ");
                    ppIRExpr(s->Ist.WrTmp.data);
                }
                else {
                    ppIRStmt(s);
                }
                vex_printf("\n");
            }
        };

        void   traceIRSB(IRSB* bb) override {
            if (getFlag(CF_traceJmp)) {
                pp_call_space();
                vex_printf("Jmp: %llx \n", TC::get_cpu_ip());
            }
        };
        void traceInvoke(ADDR call, ADDR bp) {
            if (getFlag(CF_traceInvoke)) {
                pp_call_space(TC::get_cpu_ip());
                vex_printf("Call: %llx bp: %llx\n", call, bp);
            }
        }

        virtual TR::StateBase* ForkState(HWord ges) override { return new StatePrinter<ADDR, TC>(this, ges); };
        virtual TR::State_Tag call_back_hook(TR::Hook_struct const& hs) override { setFlag(hs.cflag); return (hs.cb) ? (hs.cb)(this) : Running; }
        virtual bool  StateCompression(TR::State const& next) override { return true; }
        virtual void  StateCompressMkSymbol(TR::State const& newState) override {  };
    };

};

#include "engine/guest_arch_win32.h"
#include "engine/guest_arch_win64.h"

#include "engine/guest_arch_linux32.h"
#include "engine/guest_arch_linux64.h"

namespace SP {

    using win64 = StatePrinter<Addr64, TR::win64>;
    using win32 = StatePrinter<Addr32, TR::win32>;

    using linux64 = SP::StatePrinter<Addr64, TR::linux64>;
    using linux32 = SP::StatePrinter<Addr32, TR::linux32>;
}

#endif