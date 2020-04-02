#include "guest_arch_win32.h"
#include <winternl.h>
using namespace TR;

void TR::win32::avoid_anti_debugging()
{
    // kernelbase_IsDebuggerPresent
    auto peb = mem.load<Ity_I32>(TEB() + 0x30);
    UChar v = mem.load<Ity_I8>(peb + 2);
    if (v) {
        std::cout << "hide kernelbase_IsDebuggerPresent" << std::endl;
        mem.store(peb + 2, (UChar)0);
    }
    //PEB.NtGlobalFlag
    v = mem.load<Ity_I8>(peb + 0x68);
    if (v == 0x70) {
        std::cout << "hide PEB.NtGlobalFlag" << std::endl;
        mem.store(peb + 0x68, (UChar)0);
    }
    //patch PEB.ProcessHeap.Flags/ForceFlags
    auto process_heap = mem.load<Ity_I32>(peb + 0x18);
    v = mem.load<Ity_I8>(process_heap + 0xc);
    if (v != 2) {
        std::cout << "hide PEB.ProcessHeap.Flags" << std::endl;
        mem.store(process_heap + 0xc, 2);
    }
    v = mem.load<Ity_I8>(process_heap + 0x10);
    if (v != 0) {
        std::cout << "hide PEB.ProcessHeap.ForceFlags" << std::endl;
        mem.store(process_heap + 0x10, 0);
    }
    
}

//https://docs.microsoft.com/en-us/windows/win32/devnotes/ntreadfile
State_Tag TR::win32::Sys_syscall() 
{
    goto_ptr(vex_pop());
    m_InvokStack.pop();
    auto eax = regs.get<Ity_I32>(X86_IR_OFFSET::EAX);
    auto arg0 = vex_stack_get(1);
    auto arg1 = vex_stack_get(2);
    auto arg2 = vex_stack_get(3);
    auto arg3 = vex_stack_get(4);
    auto arg4 = vex_stack_get(5);
    auto arg5 = vex_stack_get(6);
    auto arg6 = vex_stack_get(7);


    if (eax.real()) {//这就非常的烦
        switch ((UInt)eax) {
        case 0x0000018: {//ntdll_NtAllocateVirtualMemory
            /*
            HANDLE ProcessHandle,
            PVOID *BaseAddress,
            ULONG ZeroBits,
            PULONG AllocationSize,
            ULONG AllocationType,
            ULONG Protect
            */

            UInt BaseAddress = mem.load<Ity_I32>(arg1);
            UInt RegionSize = mem.load<Ity_I32>(arg3);;
            mem.map(BaseAddress, RegionSize);

            regs.set(X86_IR_OFFSET::EAX, 0);
            return Running;
        }
        case 0x19: {//ntdll_NtQueryInformationProcess
            _In_      HANDLE           ProcessHandle = (HANDLE)(DWORD)arg0;
            _In_      PROCESSINFOCLASS ProcessInformationClass = (PROCESSINFOCLASS)(DWORD)arg1;
            _Out_     PVOID            ProcessInformation = (PVOID)(DWORD)arg2;
            _In_      DWORD            ProcessInformationLength = arg3;
            _Out_opt_ DWORD            ReturnLength = arg4;

            if (ProcessInformationClass == ProcessDebugPort) {//kernelbase_CheckRemoteDebuggerPresent
                mem.store((Addr32)(ULong)ProcessInformation, 0);
                std::cout << "war: ntdll_NtQueryInformationProcess(,,ProcessDebugPort,) hide" << std::endl;

            }
            if (ProcessInformationClass == 37) {//

            }
            regs.set(X86_IR_OFFSET::EAX, 0);
            return Running;
        }
        case 0x43: {
            PWOW64_CONTEXT ctx = (PWOW64_CONTEXT)(DWORD)arg0;
            //Addr32 next = dirty_call("getExecptionCtx32", Kc32::getExecptionCtx, { Vns(ctx), Vns(getGSPTR()) }, Ity_I32);
            //goto_ptr(next);
            m_InvokStack.clear();
            regs.set(X86_IR_OFFSET::EAX, 0);
            return Running;
        }
        case 0x01a0006: {//ntdll_NtReadFile
            /*
            NTSTATUS NtReadFile(
              _In_     HANDLE           FileHandle,
              _In_opt_ HANDLE           Event,
              _In_opt_ PIO_APC_ROUTINE  ApcRoutine,
              _In_opt_ PVOID            ApcContext,
              _Out_    PIO_STATUS_BLOCK IoStatusBlock,
              _Out_    PVOID            Buffer,
              _In_     ULONG            Length,
              _In_opt_ PLARGE_INTEGER   ByteOffset,
              _In_opt_ PULONG           Key
            );
            */


            rsval<Addr32> count = m_vctx.get_hook_read()(*this, arg5, arg6);
            //mem.store(arg4, count.concat(rsval<int>(m_ctx, 0)));
            regs.set(X86_IR_OFFSET::EAX, 1);
            return Running;
        }
        case 0x01a0008: {//ntdll_NtWriteFile
            /*
            NTSTATUS NtReadFile(
              _In_     HANDLE           FileHandle,
              _In_opt_ HANDLE           Event,
              _In_opt_ PIO_APC_ROUTINE  ApcRoutine,
              _In_opt_ PVOID            ApcContext,
              _Out_    PIO_STATUS_BLOCK IoStatusBlock,
              _Out_    PVOID            Buffer,
              _In_     ULONG            Length,
              _In_opt_ PLARGE_INTEGER   ByteOffset,
              _In_opt_ PULONG           Key
            );
            */

            m_vctx.get_hook_write()(*this, arg5, arg6);
            //mem.Ist_Store(arg4, arg6.Concat(Vns(0)));
            regs.set(X86_IR_OFFSET::EAX, 0);
            return Running;
        }
        case 0x01b0007: {//ntdll_NtDeviceIoControlFile


            regs.set(X86_IR_OFFSET::EAX, 0);
            return Running;
        }
        }

    }
    std::cerr << std::hex << get_cpu_ip() << ": Sys_syscall_windows(id:" << eax << ", arg0:" << arg0 << ", arg1:" << arg1 << ", arg2:" << arg2 << ", arg3:" << arg3 << ", arg4:" << arg4 << ", arg5:" << arg5 << ") not define" << std::endl;
    std::cerr << "Invok Stack :\n" << m_InvokStack << std::endl;
    return Death;
}

State_Tag TR::win32::Ijk_call(IRJumpKind kd)
{
    switch (kd) {
    case Ijk_Sys_syscall: {
        return Sys_syscall();
    }
    case Ijk_NoDecode: {
        //EA 09 60 47 77 33 00 00
        if ((ULong)mem.load<Ity_I64>(get_cpu_ip()) == 0x3377476009ea) {
            return Sys_syscall();
        }
        if ((UChar)mem.load<Ity_I8>(get_cpu_ip()) == 0xf2) {
            set_delta(1);
            return Running;
        }
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
        vex_printf("guest address: %p jmp kind: ", get_cpu_ip());
        ppIRJumpKind(kd);
        vex_printf("\n");
    }
    return Death;
}


void TR::win32::cpu_exception(Expt::ExceptionBase const& e)
{
    std::cerr << "Error message:" << std::endl;
    std::cerr << e << std::endl;
    UInt stack_size = sizeof(EXCEPTION_RECORD32) + sizeof(WOW64_CONTEXT);
    UInt sp_tmp = regs.get<Ity_I32>(X86_IR_OFFSET::ESP);
    UInt esp = sp_tmp - 532;


    PWOW64_CONTEXT ContextRecord = (PWOW64_CONTEXT)(esp - sizeof(WOW64_CONTEXT));
    PEXCEPTION_RECORD32 ExceptionRecord = (PEXCEPTION_RECORD32)(esp - sizeof(WOW64_CONTEXT) - sizeof(EXCEPTION_RECORD32));
    Addr64 gst;
    DWORD ExceptionCode, ExceptionAddress, ExceptionFlags, NumberParameters, nextExceptionRecord;
    DWORD info0, info1, info2;

    switch (e.errTag()) {
    case Expt::GuestMem_read_err: {
        gst = getGSPTR();
        ExceptionCode = EXCEPTION_ACCESS_VIOLATION;
        ExceptionAddress = get_cpu_ip();
        NumberParameters = 0;
        nextExceptionRecord = 0;
        ExceptionFlags = 0;
        info0 = 0;//error read
        info1 = e.addr();//error read addr
        info2 = 0;
    }
    case Expt::GuestMem_write_err: {
        gst = getGSPTR();
        ExceptionCode = EXCEPTION_ACCESS_VIOLATION;
        ExceptionAddress = get_cpu_ip();
        NumberParameters = 0;
        nextExceptionRecord = 0;
        ExceptionFlags = 0;
        info0 = 1;//write read
        info1 = e.addr();//error write addr
        info2 = 0;
    }
    case Expt::GuestRuntime_exception: {
        gst = getGSPTR();
        switch (e.jkd()) {
        case Ijk_SigTRAP:
            ExceptionCode = EXCEPTION_BREAKPOINT;
            ExceptionAddress = get_cpu_ip();
            NumberParameters = 0;
            nextExceptionRecord = 0;
            ExceptionFlags = 0;
            info0 = 0;
            info1 = 0;
            info2 = 0;
            break;
        default:
            set_status(Death);
            return;
        }
        break;
    }
    default:
        set_status(Death);
        return;
    }


    //std::cout << " SEH Exceptions at:" << std::hex << guest_start << " \nGoto handel:" << seh_exception_method << std::endl;

   /* Vns eflags = z3_x86g_calculate_eflags_all(regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::CC_OP), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::CC_DEP1), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::CC_DEP2), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::CC_NDEP));
    dirty_call("putExecptionCtx32", Kc32::putExecptionCtx,
        {
            Vns(ExceptionRecord), Vns(ContextRecord),
            Vns(gst), eflags,
            Vns(ExceptionCode), Vns(ExceptionAddress), Vns(ExceptionFlags),Vns(NumberParameters), Vns(nextExceptionRecord),
            Vns(info0), Vns(info1), Vns(info2)
        },
        Ity_I32);*/

    regs.set(X86_IR_OFFSET::ESP, esp - stack_size);
    vex_push((Addr32)(ULong)ContextRecord);
    vex_push((Addr32)(ULong)ExceptionRecord);

    Addr32 ntdll_KiUserExceptionDispatcher = (Addr32)m_vctx.param().get("ntdll_KiUserExceptionDispatcher");
    if (!ntdll_KiUserExceptionDispatcher) {
        std::cerr << "(ctx32).param().set(\"ntdll_KiUserExceptionDispatcher\", 0x-----);" << std::endl;
        set_status(Death);
        return;
    }
    else {
        goto_ptr(ntdll_KiUserExceptionDispatcher);
        set_status(Exception);
    }

}




