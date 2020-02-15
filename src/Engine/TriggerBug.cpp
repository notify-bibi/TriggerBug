﻿/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    TriggerBug.cpp: 
Abstract:
    API list;
Author:
    WXC 2019-05-31.
Revision History:
--*/


//#undef _DEBUG
#define DLL_EXPORTS



#include "engine.hpp"
#include "Variable.hpp"
#include "Register.hpp"
#include "memory.hpp"
#include "../Thread_Pool/ThreadPool.hpp"
#include "SimulationEngine/State_class.hpp"
#include "SimulationEngine/State_analyzer.hpp"
#include "Z3_Target_Call/Guest_Helper.hpp"



UInt flag_count = 0;
UInt flag_max_count = 0;
extern "C" void dfd();

namespace SP {
    template <typename ADDR, class TC>
    class StatePrinter;
};

class StateX86 : public State<Addr32> {
    friend class SP::StatePrinter<Addr32, StateX86>;
    ULong g_brk = ALIGN(0x0000000000603000, 32);
    StateX86(StateX86* father_state, Addr32 gse) :State(father_state, gse) {};
public:
    StateX86(const char* filename, Addr32 gse, Bool _need_record) :State(filename, gse, _need_record) {};
    

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
        case Ijk_Sys_syscall:
            return Sys_syscall();
        default:
            vex_printf("guest address: %p jmp kind: ", guest_start);
            ppIRJumpKind(kd);
            vex_printf("\n");
        }
        return Death;
    }

    State_Tag Sys_syscall() {
        UChar rax = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::EAX);
        ULong rdi = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::EDI);
        ULong rdx = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::EDX);
        ULong rsi = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::ESI);
        return Death;
    }

    void* ForkState(Addr32 ges) override { return new StateX86(this, ges); };
    void* mkState(Addr32 ges) override { return (State<Addr32>*)(StateX86*)ForkState(ges); }
};


class StateAMD64 : public State<Addr64> {
    ULong g_brk = ALIGN(0x0000000000603000, 32);
    friend class SP::StatePrinter<Addr64, StateAMD64>;
    StateAMD64(StateAMD64* father_state, Addr64 gse) :
        State(father_state, gse)
    {
    };
public:
    StateAMD64(const char* filename, Addr64 gse, Bool _need_record) :
        State(filename, gse, _need_record)
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
        case Ijk_Sys_syscall:
            switch (guest_system) {
            case linux:return Sys_syscall_linux();
            }
        default:
            vex_printf("guest address: %p . error jmp kind: ", guest_start);
            ppIRJumpKind(kd);
            vex_printf("\n");
        }
    }

    State_Tag Sys_syscall_linux() {
        Vns al = regs.Iex_Get<Ity_I8>(AMD64_IR_OFFSET::RAX);
        if (al.real()) {
            Vns rdi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RDI);
            Vns rdx = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RDX);
            Vns rsi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RSI);
            switch ((UChar)al) {
            case 0:// //LINUX - sys_read
                if (rdi == 0) {
                    for (ULong n = 0; n < rdx; n++) {
                        if (flag_count >= flag_max_count) {
                            mem.Ist_Store(rsi + n, '\n');
                        }
                        else {
                            Vns FLAG = mk_int_const(8);
                            mem.Ist_Store(rsi + n, FLAG);
                            auto ao1 = FLAG >= 'A' && FLAG <= 'Z';
                            auto ao2 = FLAG >= 'a' && FLAG <= 'z';
                            auto ao3 = FLAG >= '0' && FLAG <= '9';
                            solv.add_assert(ao1 || ao2 || ao3 || FLAG == '_' || FLAG == '{' || FLAG == '}', True);
                        }
                    }
                    regs.Ist_Put(AMD64_IR_OFFSET::RAX, rdx);
                    flag_count += rdx;
                    return Running;
                }
            case 1: {//LINUX - sys_write
                for (ULong n = 0; n < rdx; n++) {
                    UChar chr = mem.Iex_Load<Ity_I8>(rsi + n);
                    vex_printf("%c", chr);
                }
                regs.Ist_Put(AMD64_IR_OFFSET::RAX, rdx);
                return Running;
            }

            case 0x3: {//LINUX - sys_close
                vex_printf("system call: sys_close description:0x%x\n", rdi);
                regs.Ist_Put(AMD64_IR_OFFSET::RAX, 1);
                break;
            }
            case 0x5: {//LINUX - sys_newfstat
                vex_printf("system call: sys_newfstat\tfd:0x%x 	struct stat __user *statbuf:0x%x", (ULong)rdi, (ULong)rsi);
                regs.Ist_Put(AMD64_IR_OFFSET::RAX, 0ull);
                return Running;
            }

            case 0xC: {//LINUX - sys_brk
                ULong rbx = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RBX);
                vex_printf("system call: brk address:0x%x\n", rbx);
                ULong brk = rbx;
                if (brk) {
                    if (brk < g_brk) {
                        mem.unmap(brk, g_brk);
                        g_brk = ALIGN(brk, 32);
                    }
                    else if (brk == g_brk) {
                        mem.map(g_brk, g_brk + 0x21000);
                        g_brk = ALIGN(g_brk + 0x21000, 32);
                    }
                    else {
                        mem.map(g_brk, brk);
                        g_brk = ALIGN(brk, 32);
                    }
                }
                regs.Ist_Put(AMD64_IR_OFFSET::RAX, g_brk);
                return Running;
            }
            case 0x23: {//LINUX - sys_nanosleep
                vex_printf("system call: sys_nanosleep\n");
                return Running;
            }
            case 0xE7: {//LINUX - sys_Exit
                vex_printf("system call: sys_Exit\n");
                return Exit;
            }
            case 0x101: {//LINUX - sync_file_range
                // rsi filename   rdx flag
                std::stringstream filename;
                if (rsi.real()) {
                    UInt p = getStr(filename, rsi);
                    if (p == -1) {
                        vex_printf("system call: sync_file_range\tname:%s flag:0x%x", filename.str().c_str(), (ULong)rdx);

                        //result = state.file_system.sync_file_range(filename = filename, flags = rdx)
                        //setRax(state, result)
                    }
                }
                break;
            }

            }
            vex_printf("system call: sys_ %d\n", (UChar)al);
        }
       
        return Death;
    }

    virtual void* ForkState(Addr64 ges) override { return new StateAMD64(this, ges); };
    virtual void* mkState(Addr64 ges) override { return (State<Addr64>*)(StateAMD64*)ForkState(ges); }
};




namespace SP {

    template <typename ADDR, class TC>
    class StatePrinter : public TC {
        friend GraphView;
        TRControlFlags trtraceflags;
    public:
        StatePrinter(StatePrinter* father_state, ADDR gse) : TC(father_state, gse), trtraceflags(father_state->trtraceflags) {};
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
                    std::cout << ir_temp[tmp];
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

        
        virtual void* ForkState(ADDR ges) override { return new StatePrinter<ADDR, TC>(this, ges); };
        virtual void* mkState(ADDR ges) override { return (State<ADDR>*)(StatePrinter<ADDR, TC>*)ForkState(ges); }
        virtual State_Tag call_back_hook(Hook_struct const& hs) override { setFlag(hs.cflag); return (hs.cb) ? (hs.cb)(this) : Running; }
    };

    using AMD64 = StatePrinter<Addr64, StateAMD64>;
    using X86 = StatePrinter<Addr32, StateX86>;
}


//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\TriggerBug-asong.xml"
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\Roads\\Roads.xml"
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\puzzle\\puzzle.xml"
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\reverse\\c++symbol\\childRE.xml"


//
//State_Tag success_ret(Kernel* _s) {
//    vex_printf("success_ret  ??????????\n\n%d");
//    return (State_Tag)0x999;
//
//    s->solv.push();
//    auto ecx = s->regs.Iex_Get<Ity_I32>(12);
//    auto edi = s->regs.Iex_Get<Ity_I32>(36);
//
//    for (int i = 0; i < 44; i++) {
//        auto al = s->mem.Iex_Load<Ity_I8>(ecx + i);
//        auto bl = s->mem.Iex_Load<Ity_I8>(edi + i);
//        s->solv.add(al == bl);
//    }
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("sat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    return Death;
//}
//
//
//State_Tag success_ret2(State* s) {
//
//    s->solv.push();
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("sat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    exit(1);
//    return Death;
//}
//
//
State_Tag success_ret3(Kernel* _s) {
    State<Addr32>* s = *_s;
    s->solv.push();
    UChar bf[] = { 0xEC, 0x29, 0xE3, 0x41, 0xE1, 0xF7, 0xAA, 0x1D, 0x29, 0xED, 0x29, 0x99, 0x39, 0xF3, 0xB7, 0xA9, 0xE7, 0xAC, 0x2B, 0xB7, 0xAB, 0x40, 0x9F, 0xA9, 0x31, 0x35, 0x2C, 0x29, 0xEF, 0xA8, 0x3D, 0x4B, 0xB0, 0xE9, 0xE1, 0x68, 0x7B, 0x41 };

    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RDI);
    for (int i = 0; i < 38; i++) {
        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
        s->solv.add(e == (UChar)bf[i]);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == sat) {
        vex_printf("issat");
        auto m = s->solv.get_model();
        std::cout << m << std::endl;
        exit(0);
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    s->solv.pop();
    return Death;
}
//
//
//State_Tag success_ret33(State* s) {
//    s->solv.push();
//    UChar bf[] = { 133, 67, 104, 133, 245, 38, 60, 61, 39, 245, 51, 104, 62, 60, 118, 38, 245, 118, 165, 245, 19, 165, 61, 245, 62, 165, 45, 61, 245, 7, 60, 118, 29, 60, 15, 0, 133, 169 };
//
//    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rax);
//    for (int i = 0; i < 38; i++) {
//        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
//        s->solv.add(e == (UChar)bf[i]);
//    }
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("issat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//        exit(0);
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    return Death;
//}
//
//
//State_Tag whil(State* s) {
//    return (State_Tag)0x233;
//}
//
//State_Tag pp(State* s) {
//    auto al = s->regs.Iex_Get<Ity_I32>(AMD64_IR_OFFSET::eax);
//    std::cout << Z3_ast_to_string(al, al) << std::endl;
//    s->regs.Ist_Put(AMD64_IR_OFFSET::rax, 38ull);
//    s->hook_pass(5);
//    return (State_Tag)Running;
//}
//
//State_Tag Dea(State* s) {
//    return (State_Tag)Death;
//}



#include "SimulationEngine/Z3_Target_Call/Guest_Helper.hpp"

Vns flag_limit(Vns &flag) {
    char flags_char[] = "@_-{}1:() ^";
    Vns re = Vns(flag, flags_char[0]) == flag;
    for (int i = 1; i < sizeof(flags_char); i++) {
        re = re || (Vns(flag, flags_char[i]) == flag);
    }
    auto ao1 = flag >= 'a' && flag <= 'z';
    auto ao2 = flag >= 'A' && flag <= 'Z';
    auto ao3 = flag >= '0' && flag <= '9';
    return re || ao1 || ao2 || ao3;
}


#include "example.hpp"
 

int main() {
    SP::AMD64 state("C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.xml", 0, True);
    std::cout << state << std::endl;

    TRGL::VexGuestAMD64State reg(state);
    /*for (int i = 0; i < 38; i++) {
        auto flag = state.mk_int_const(8);
        auto ao3 = flag >= 1 && flag <= 128;
        state.mem.Ist_Store(reg.guest_RDI + i, flag);
        state.solv.add_assert(ao3);
    }*/
    state.hook_add(0x400CC0, success_ret3);

    
    StateAnalyzer<Addr64> gv(state);
    gv.Run();
}

//int main() {
//    {
//        flag_max_count = 38+6;
//        flag_count = 0;
//
//        StatePrinter<StateAMD64> state(INIFILENAME, 0, True);
//        state.hook_add(0x400CC0, success_ret3);
//        StateAnalyzer gv(state);
//        gv.Run();
//    };
//    return 0;
//}

//
//int main() {
//    flag_max_count = 1;
//    flag_count = 0;
//
//    StatePrinter<StateX86> state(INIFILENAME, 0, True);
//
//    context& c = state;
//
//    for (int i = 0; i < 32; i++) {
//        auto flag = state.get_int_const(8);
//        auto ao1 = flag >= 'a' && flag <= 'f';
//        auto ao3 = flag >= '0' && flag <= '9';
//        state.mem.Ist_Store(i + 0x0019F554, flag);
//        state.add_assert(ao1 || ao3, 1);
//        if (i == 31) {
//            _VexGuestX86State reg(state);
//            state.mem.Ist_Store(reg.guest_EBP-0x24, flag);
//        }
//    }
//
//
//    state.hook_add(0x4050B0, Dea);
//    state.hook_add(0x4050D0, success_ret2);
//
//    State::pushState(state);
//    State::pool->wait();
//
//    return 0;
//}


//