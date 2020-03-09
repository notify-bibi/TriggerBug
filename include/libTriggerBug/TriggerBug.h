#ifndef _TRIGGERBUG_
#define _TRIGGERBUG_

#include "engine.hpp"
#include "Variable.hpp"
#include "Register.hpp"
#include "memory.hpp"
#include "thread_pool/ThreadPool.h"
#include "engine/State_class.hpp"
#include "engine/State_analyzer.hpp"

namespace SP {
    template <typename ADDR, class TC>
    class StatePrinter;
};

class StateX86 : public State<Addr32> {
    friend class SP::StatePrinter<Addr32, StateX86>;
    ULong g_brk = ALIGN(0x0000000000603000, 32);
    StateX86(StateX86* father_state, Addr32 gse) :State(father_state, gse) {};
public:
    StateX86(Vex_Info& vex_info, Addr32 gse, Bool _need_record) :State(vex_info, gse, _need_record) {};


    void cpu_exception() override {
        UInt seh_addr = x86g_use_seg_selector(regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::LDT), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::GDT), regs.Iex_Get<Ity_I16>(X86_IR_OFFSET::FS).zext(16), 0);
        Vns seh = mem.Iex_Load<Ity_I32>(seh_addr);
        Vns next = mem.Iex_Load<Ity_I32>(seh);
        Vns seh_exception_method = mem.Iex_Load<Ity_I32>(seh + 4);
        set_status(Exception);
        std::cout << " SEH Exceptions at:" << std::hex << guest_start << " \nGoto handel:" << seh_exception_method << std::endl;
        guest_start = seh_exception_method;

        /*  esp & ebp  不正确的esp*/
        regs.Ist_Put(X86_IR_OFFSET::ESP, seh);

        exit(2);
    }

    State_Tag Ijk_call(IRJumpKind kd) override {
        switch (kd) {
        case Ijk_Sys_syscall: {
            switch (info().guest_system) {
            case linux:return Sys_syscall_linux();
            }
            return Death;
        }
        case Ijk_NoDecode:  return NoDecode;
        default:
            vex_printf("guest address: %p jmp kind: ", guest_start);
            ppIRJumpKind(kd);
            vex_printf("\n");
        }
        return Death;
    }

    State_Tag Sys_syscall_linux() {
        UChar rax = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::EAX);
        ULong rdi = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::EDI);
        ULong rdx = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::EDX);
        ULong rsi = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::ESI);
        return Death;
    }

    Kernel* ForkState(Addr32 ges) override { return new StateX86(this, ges); };
};


class StateAMD64 : public State<Addr64> {
    ULong g_brk = ALIGN(0x0000000000603000, 32);
    friend class SP::StatePrinter<Addr64, StateAMD64>;
    StateAMD64(StateAMD64* father_state, Addr64 gse) :
        State(father_state, gse)
    {
    };
public:
    StateAMD64(Vex_Info& vex_info, Addr64 gse, Bool _need_record) :
        State(vex_info, gse, _need_record)
    {
    };


    void cpu_exception() override {
        set_status(Death);
        //UInt seh_addr = x86g_use_seg_selector(regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::ldt), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::gdt), regs.Iex_Get<Ity_I16>(X86_IR_OFFSET::fs).zext(16), 0);
        //Vns seh = mem.Iex_Load<Ity_I32>(seh_addr);
        //Vns next = mem.Iex_Load<Ity_I32>(seh);
        //Vns seh_exception_method = mem.Iex_Load<Ity_I32>(seh + 4);
        //status = Exception;
        //std::cout << " SEH Exceptions at:" << std::hex << guest_start << " \nGoto handel:" << seh_exception_method << std::endl;
        //guest_start = seh_exception_method;

        ///*  esp & ebp  不正确的esp*/
        //regs.Ist_Put(X86_IR_OFFSET::esp, seh);

        //exit(2);
    }

    State_Tag Ijk_call(IRJumpKind kd) override {
        switch (kd) {
        case Ijk_Sys_syscall: {
            switch (info().guest_system) {
            case linux:return Sys_syscall_linux();
            }
            return Death;
        }
        case Ijk_NoDecode:  return NoDecode;
        default:
            vex_printf("guest address: %p . error jmp kind: ", guest_start);
            ppIRJumpKind(kd);
            vex_printf("\n");
        }
    }

    State_Tag Sys_syscall_linux();
    virtual Kernel* ForkState(Addr64 ges) override { return new StateAMD64(this, ges); };
    virtual bool  StateCompression(State const& next) override { return true; }
    virtual void  StateCompressMkSymbol(State const& newState) override {  };
};




namespace SP {

    template <typename ADDR, class TC>
    class StatePrinter : public TC {
        TRControlFlags trtraceflags;
    public:
        StatePrinter(StatePrinter* father_state, ADDR gse) : TC(father_state, gse), trtraceflags(father_state->trtraceflags) {};
        inline bool getFlag(TRControlFlags t) const { return trtraceflags & t; }
        inline void setFlag(TRControlFlags t) { *(ULong*)&trtraceflags |= t; }
        inline void unsetFlag(TRControlFlags t) { *(ULong*)&trtraceflags &= ~t; };
        inline TRControlFlags gtrtraceflags() { return trtraceflags; }
    public:
        StatePrinter(Vex_Info& vex_info, ADDR gse, Bool _need_record) :
            TC(vex_info, gse, _need_record),
            trtraceflags(CF_None) {
            trtraceflags = (TRControlFlags)info().getFlags();
        };


        void   traceStart() override {
            if (getFlag(CF_traceState))
                std::cout << "\n+++++++++++++++ Thread ID: " << GetCurrentThreadId() << "  address: " << std::hex << guest_start << "  Started +++++++++++++++\n" << std::endl;
        };

        void   traceFinish() override {
            if (getFlag(CF_traceState)) {
                if (status() == Fork) {
                    vex_printf("Fork from: %p to:{ ", guest_start);
                    for (auto bc : branch) {
                        vex_printf(" %p", bc->get_state_ep());
                    }
                    vex_printf(" };", guest_start);
                }
                std::cout << "\n+++++++++++++++ Thread ID: " << GetCurrentThreadId() << "  address: " << std::hex << guest_start << "  OVER +++++++++++++++\n" << std::endl;
            }
        }

        void   traceIRStmtEnd(IRStmt* s) override {
            if (getFlag(CF_ppStmts)) {
                if (s->tag == Ist_WrTmp) {
                    UInt tmp = s->Ist.WrTmp.tmp;
                    vex_printf("t%u = ", tmp);
                    std::cout << m_ir_temp[tmp];
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
                vex_printf("Jmp: %llx \n", guest_start);
            }
        };


        virtual Kernel* ForkState(ADDR ges) override { return new StatePrinter<ADDR, TC>(this, ges); };
        virtual State_Tag call_back_hook(Hook_struct const& hs) override { setFlag(hs.cflag); return (hs.cb) ? (hs.cb)(this) : Running; }
        virtual bool  StateCompression(State<ADDR> const& next) override { return true; }
        virtual void  StateCompressMkSymbol(State<ADDR> const& newState) override {  };
    };

    using AMD64 = StatePrinter<Addr64, StateAMD64>;
    using X86 = StatePrinter<Addr32, StateX86>;
};



#endif