#include "guest_arch_linux32.h"

using namespace TR;


void TR::linux32::avoid_anti_debugging()
{
}

State_Tag TR::linux32::Sys_syscall()
{
    auto eax = regs.get<Ity_I32>(X86_IR_OFFSET::EAX);
    auto edi = regs.get<Ity_I32>(X86_IR_OFFSET::EDI);
    auto edx = regs.get<Ity_I32>(X86_IR_OFFSET::EDX);
    auto esi = regs.get<Ity_I32>(X86_IR_OFFSET::ESI);
    return Death;
}

State_Tag TR::linux32::Ijk_call(IRJumpKind kd)
{
    switch (kd) {
    case Ijk_Sys_syscall: {
        return Sys_syscall();
    }
    case Ijk_NoDecode: {
        std::cerr << "Error message: valgrind Ijk_NoDecode " << std::hex << get_cpu_ip() << std::endl;
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
}

void TR::linux32::cpu_exception(Expt::ExceptionBase const& e)
{
}
