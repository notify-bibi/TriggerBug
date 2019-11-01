/*++
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
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\TriggerBug-asong.xml"
#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.xml"
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\Roads\\Roads.xml"


#include "engine.hpp"
#define vpanic(...) printf("%s line %d",__FILE__,__LINE__); vpanic(__VA_ARGS__);

#include "SimulationEngine/State_analyzer.hpp"
#include "Z3_Target_Call/Guest_Helper.hpp"



UInt flag_count = 0;
UInt flag_max_count = 0;

class StateX86 : public State {
public:
    StateX86(const char* filename, Addr64 gse, Bool _need_record) :
        State(filename, gse, _need_record)
    {
    };

    StateX86(StateX86* father_state, Addr64 gse) :
        State(father_state, gse)
    {
    };

    void cpu_exception() {
        UInt seh_addr = x86g_use_seg_selector(regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::ldt), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::gdt), regs.Iex_Get<Ity_I16>(X86_IR_OFFSET::fs).zext(16), 0);
        Vns seh = mem.Iex_Load<Ity_I32>(seh_addr);
        Vns next = mem.Iex_Load<Ity_I32>(seh);
        Vns seh_exception_method = mem.Iex_Load<Ity_I32>(seh + 4);
        status = Exception;
        std::cout << " SEH Exceptions at:" << std::hex << guest_start << " \nGoto handel:" << seh_exception_method << std::endl;
        guest_start = seh_exception_method;

        /*  esp & ebp  不正确的esp*/
        regs.Ist_Put(X86_IR_OFFSET::esp, seh);

        exit(2);
    }

    State_Tag Ijk_call(IRJumpKind kd) {
        switch (kd) {
        case Ijk_Sys_syscall:
            return Sys_syscall();
        default:
            return Death;
        }
    }

    State_Tag Sys_syscall() {
        UChar rax = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::eax);
        ULong rdi = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::edi);
        ULong rdx = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::edx);
        ULong rsi = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::esi);
        return Death;
    }

    State* ForkState(ADDR ges) {
        return new StateX86(this, ges);
    };

};


class StateAMD64 : public State {
    ULong g_brk = ALIGN(0x000000000060A000, 32);
public:
    StateAMD64(const char* filename, Addr64 gse, Bool _need_record) :
        State(filename, gse, _need_record)
    {
    };

    StateAMD64(StateAMD64* father_state, Addr64 gse) :
        State(father_state, gse)
    {
    };

    void cpu_exception() {
        UInt seh_addr = x86g_use_seg_selector(regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::ldt), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::gdt), regs.Iex_Get<Ity_I16>(X86_IR_OFFSET::fs).zext(16), 0);
        Vns seh = mem.Iex_Load<Ity_I32>(seh_addr);
        Vns next = mem.Iex_Load<Ity_I32>(seh);
        Vns seh_exception_method = mem.Iex_Load<Ity_I32>(seh + 4);
        status = Exception;
        std::cout << " SEH Exceptions at:" << std::hex << guest_start << " \nGoto handel:" << seh_exception_method << std::endl;
        guest_start = seh_exception_method;

        /*  esp & ebp  不正确的esp*/
        regs.Ist_Put(X86_IR_OFFSET::esp, seh);

        exit(2);
    }

    State_Tag Ijk_call(IRJumpKind kd) {
        switch (kd) {
        case Ijk_Sys_syscall:
            switch (guest_system) {
            case linux:return Sys_syscall_linux();
            }
        default:
            return Death;
        }
    }

    State_Tag Sys_syscall_linux() {
        UChar al = regs.Iex_Get<Ity_I8>(AMD64_IR_OFFSET::rax);
        ULong rdi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rdi);
        ULong rdx = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rdx);
        ULong rsi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rsi);
        switch (al) {
        case 0:// //LINUX - sys_read
            if (rdi == 0) {
                for (ULong n = 0; n < rdx; n++) {
                    if (flag_count >= flag_max_count) {
                        mem.Ist_Store(rsi + n, '\n');
                    }
                    else {
                        Vns FLAG = get_int_const(8);
                        mem.Ist_Store(rsi + n, FLAG);
                        auto ao1 = FLAG >= 'A' && FLAG <= 'Z';
                        auto ao2 = FLAG >= 'a' && FLAG <= 'z';
                        auto ao3 = FLAG >= '0' && FLAG <= '9';
                        add_assert(ao1 || ao2 || ao3, True);
                    }
                }
                regs.Ist_Put(AMD64_IR_OFFSET::rax, rdx);
                flag_count += rdx;
                return Running;
            }
        case 1: {//LINUX - sys_write
            for (ULong n = 0; n < rdx; n++) {
                UChar chr = mem.Iex_Load<Ity_I8>(rsi + n);
                vex_printf("%c", chr);
            }
            regs.Ist_Put(AMD64_IR_OFFSET::rax, rdx);
            return Running;
        }

        case 0xC: {//LINUX - sys_brk
            ULong rbx = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rbx);
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
            regs.Ist_Put(AMD64_IR_OFFSET::rax, g_brk);
            return Running;
        }
        case 0x23: {//LINUX - sys_nanosleep
            vex_printf("system call: sys_nanosleep\n");
        }
        case 0xE7: {//LINUX - sys_Exit
            vex_printf("system call: sys_Exit\n");
        }
        }
        return Death;
    }

    State* ForkState(ADDR ges) {
        return new StateAMD64(this, ges);
    };
};









State_Tag success_ret(State* s) {
    s->solv.push();
    auto ecx = s->regs.Iex_Get<Ity_I32>(12);
    auto edi = s->regs.Iex_Get<Ity_I32>(36);

    for (int i = 0; i < 44; i++) {
        auto al = s->mem.Iex_Load<Ity_I8>(ecx + i);
        auto bl = s->mem.Iex_Load<Ity_I8>(edi + i);
        s->add_assert_eq(al, bl);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == sat) {
        vex_printf("sat");
        auto m = s->solv.get_model();
        std::cout << m << std::endl;
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    s->solv.pop();
    return Death;
}





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
    flag_max_count = 1;
    flag_count = 0;


    StatePrinter<StateAMD64> state(INIFILENAME, (Addr64)0, True);

    _VexGuestAMD64State v(state);
    ULong i = v.guest_RIP;

   // state.mem.Ist_Store(0x0007F93588377B8 + 1, (UChar)0xae);
    context& c = state;
    StateAnalyzer sa(state);
    sa.Run();

    printf("OVER");
    getchar();
    return 0;
}




