#include "guest_arch_win64.h"
#include <winternl.h>
using namespace TR;

void TR::win64::avoid_anti_debugging()
{
}

State_Tag TR::win64::Sys_syscall()
{
}

State_Tag TR::win64::Ijk_call(IRJumpKind kd)
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



void TR::win64::cpu_exception(Expt::ExceptionBase const& e)
{
}
