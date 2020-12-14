#ifdef _MSC_VER
#include "guest_arch_win32.h"
#include <Windows.h>
#include <winternl.h>
using namespace TR;

//namespace Kc32 {
//    VOID putExecptionCtx(
//        PEXCEPTION_RECORD32 ExceptionRecord, PWOW64_CONTEXT ContextRecord,
//        VexGuestX86State* gst, DWORD eflags,
//        DWORD ExceptionCode, DWORD ExceptionAddress, DWORD ExceptionFlags, DWORD NumberParameters, DWORD  nextExceptionRecord,
//        DWORD info0, DWORD info1, DWORD info2);
//    UInt getExecptionCtx(IN PWOW64_CONTEXT ContextRecord, OUT VexGuestX86State* gst);
//};

void TR::win32::avoid_anti_debugging()
{
    // kernelbase_IsDebuggerPresent
    auto peb = mem.load<Ity_I32>(TEB() + 0x30);
    if (peb.real()) {
        UChar v = mem.load<Ity_I8>(peb + 2).tor();
        if (v) {
            std::cout << "hide kernelbase_IsDebuggerPresent" << std::endl;
            mem.store(peb + 2, (UChar)0);
        }
        //PEB.NtGlobalFlag
        v = mem.load<Ity_I8>(peb + 0x68).tor();
        if (v == 0x70) {
            std::cout << "hide PEB.NtGlobalFlag" << std::endl;
            mem.store(peb + 0x68, (UChar)0);
        }
        //patch PEB.ProcessHeap.Flags/ForceFlags
        auto process_heap = mem.load<Ity_I32>(peb + 0x18);
        v = mem.load<Ity_I8>(process_heap + 0xc).tor();
        if (v != 2) {
            std::cout << "hide PEB.ProcessHeap.Flags" << std::endl;
            mem.store(process_heap + 0xc, 2);
        }
        v = mem.load<Ity_I8>(process_heap + 0x10).tor();
        if (v != 0) {
            std::cout << "hide PEB.ProcessHeap.ForceFlags" << std::endl;
            mem.store(process_heap + 0x10, 0);
        }
    }
}

//https://docs.microsoft.com/en-us/windows/win32/devnotes/ntreadfile
State_Tag TR::win32::Sys_syscall() 
{
    goto_ptr(vex_pop().tor());
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
        switch ((UInt)eax.tor()) {
        case 0x0000018: {//ntdll_NtAllocateVirtualMemory
            /*
            HANDLE ProcessHandle,
            PVOID *BaseAddress,
            ULONG ZeroBits,
            PULONG AllocationSize,
            ULONG AllocationType,
            ULONG Protect
            */

            UInt BaseAddress = mem.load<Ity_I32>(arg1).tor();
            UInt RegionSize = mem.load<Ity_I32>(arg3).tor();
            mem.map(BaseAddress, RegionSize);

            regs.set(X86_IR_OFFSET::EAX, 0);
            return Running;
        }
        case 0x19: {//ntdll_NtQueryInformationProcess
            _In_      HANDLE           ProcessHandle = (HANDLE)(size_t)(DWORD)arg0.tor();
            _In_      PROCESSINFOCLASS ProcessInformationClass = (PROCESSINFOCLASS)(DWORD)arg1.tor();
            _Out_     PVOID            ProcessInformation = (PVOID)(size_t)(DWORD)arg2.tor();
            _In_      DWORD            ProcessInformationLength = arg3.tor();
            _Out_opt_ DWORD            ReturnLength = arg4.tor();

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
            PWOW64_CONTEXT wow64_ctx = (PWOW64_CONTEXT)(size_t)(DWORD)arg0.tor();
            //Addr32 next = dirty_call("getExecptionCtx32", Kc32::getExecptionCtx, { rsval<Addr64>(ctx(), (size_t)wow64_ctx), rsval<Addr64>(ctx(), getGSPTR()) }, Ity_I32);
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
            mem.store(arg4, count.concat(rsval<int>(ctx(), 0)));
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
            mem.store(arg4, arg6.concat(rsval<int>(ctx(), 0)));
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
        if ((ULong)mem.load<Ity_I64>(get_cpu_ip()).tor() == 0x3377476009ea) {
            return Sys_syscall();
        }
        if ((UChar)mem.load<Ity_I8>(get_cpu_ip()).tor() == 0xf2) {
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
    UInt sp_tmp = regs.get<Ity_I32>(X86_IR_OFFSET::ESP).tor();
    UInt esp = sp_tmp - 532;


    PWOW64_CONTEXT ContextRecord = (PWOW64_CONTEXT)(esp - sizeof(WOW64_CONTEXT));
    PEXCEPTION_RECORD32 ExceptionRecord = (PEXCEPTION_RECORD32)(esp - sizeof(WOW64_CONTEXT) - sizeof(EXCEPTION_RECORD32));
    Addr64 gst;
    DWORD ExceptionCode, ExceptionAddress, ExceptionFlags, NumberParameters, nextExceptionRecord;
    DWORD info0, info1, info2;

    switch (e.errTag()) {
    case Expt::GuestMem_read_err: {
        //gst = getGSPTR();
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
        //gst = getGSPTR();
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
        //gst = getGSPTR();
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


    std::cout << " SEH Exception ID:[" << std::hex << ExceptionCode << "] at:" << std::hex << get_cpu_ip() << std::endl;

    auto eflags = z3_x86g_calculate_eflags_all(regs.get<Ity_I32>(X86_IR_OFFSET::CC_OP), regs.get<Ity_I32>(X86_IR_OFFSET::CC_DEP1), regs.get<Ity_I32>(X86_IR_OFFSET::CC_DEP2), regs.get<Ity_I32>(X86_IR_OFFSET::CC_NDEP));
    

    mem.map(0x100000, 99999);


 /*   dirty_call("putExecptionCtx32", Kc32::putExecptionCtx,
        {
            rcval<Addr32>(ctx(), (size_t)ExceptionRecord), rcval<Addr32>(ctx(), (size_t)ContextRecord),
            rcval<Addr64>(ctx(), gst), eflags,
            rcval<int>(ctx(), ExceptionCode), rcval<Addr32>(ctx(), ExceptionAddress), rcval<int>(ctx(), ExceptionFlags),rcval<int>(ctx(), NumberParameters), rcval<Addr32>(ctx(), nextExceptionRecord),
            rcval<Addr32>(ctx(), info0), rcval<Addr32>(ctx(), info1), rcval<Addr32>(ctx(), info2)
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




#endif