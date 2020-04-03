#include "guest_arch_linux64.h"

namespace TR {

    void TR::linux64::avoid_anti_debugging()
    {
        int hg;
        return;
    }

    State_Tag linux64::Sys_syscall() {
        auto al = regs.get<Ity_I8>(AMD64_IR_OFFSET::RAX);
        if (al.real()) {
            auto rdi = regs.get<Ity_I64>(AMD64_IR_OFFSET::RDI);
            auto rdx = regs.get<Ity_I64>(AMD64_IR_OFFSET::RDX);
            auto rsi = regs.get<Ity_I64>(AMD64_IR_OFFSET::RSI);
            switch ((UChar)al.tor()) {
            case 0:// //LINUX - sys_read
                if (rdi.tor() == 0) {
                    rsval<Addr64> count = m_vctx.get_hook_read()(*this, rsi, rdx);
                    regs.set(AMD64_IR_OFFSET::RAX, count);
                    return Running;
                }
            case 1: {//LINUX - sys_write
                m_vctx.get_hook_write()(*this, rsi, rdx);
                regs.set(AMD64_IR_OFFSET::RAX, rdx);
                return Running;
            }

            case 0x3: {//LINUX - sys_close
                vex_printf("system call: sys_close description:0x%x\n", rdi);
                regs.set(AMD64_IR_OFFSET::RAX, 1);
                break;
            }
            case 0x5: {//LINUX - sys_newfstat
                vex_printf("system call: sys_newfstat\tfd:0x%x 	struct stat __user *statbuf:0x%x", (ULong)rdi.tor(), (ULong)rsi.tor());
                regs.set(AMD64_IR_OFFSET::RAX, 0ull);
                return Running;
            }

            case 0xC: {//LINUX - sys_brk
                ULong rbx = regs.get<Ity_I64>(AMD64_IR_OFFSET::RBX).tor();
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
                regs.set(AMD64_IR_OFFSET::RAX, g_brk);
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
                    UInt p = getStr(filename, rsi.tor());
                    if (p == -1) {
                        vex_printf("system call: sync_file_range\tname:%s flag:0x%x", filename.str().c_str(), (ULong)rdx.tor());

                        //result = state.file_system.sync_file_range(filename = filename, flags = rdx)
                        //setRax(state, result)
                    }
                }
                break;
            }

            }
            std::cout << "system call: sys_" << al << std::endl;
        }

        return Death;
    }

    State_Tag linux64::Ijk_call(IRJumpKind kd)
    {
        switch (kd) {
        case Ijk_Sys_syscall: {
            return Sys_syscall();
        }
        case Ijk_NoDecode: {
            std::cerr << "Error message:" << std::hex << get_cpu_ip() << std::endl;
            return NoDecode;
        }
        case Ijk_SigILL:         /* current instruction synths SIGILL */
        case Ijk_SigTRAP:        /* current instruction synths SIGTRAP */
        case Ijk_SigSEGV:        /* current instruction synths SIGSEGV */
        case Ijk_SigBUS:         /* current instruction synths SIGBUS */
        case Ijk_SigFPE:         /* current instruction synths generic SIGFPE */
        case Ijk_SigFPE_IntDiv:  /* current instruction synths SIGFPE - IntDiv */
        case Ijk_SigFPE_IntOvf:  /* current instruction synths SIGFPE - IntOvf */
        { throw Expt::RuntimeIrSig(get_cpu_ip(), kd); }
        default:
            vex_printf("guest address: %p . error jmp kind: ", get_cpu_ip());
            ppIRJumpKind(kd);
            vex_printf("\n");
        }
        return State_Tag();
    }

    void linux64::cpu_exception(Expt::ExceptionBase const& e)
    {
    }

}
