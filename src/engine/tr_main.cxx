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


#include "engine/tr_main.h"
#include "engine/guest_helper_defs.h"
#include <winternl.h>


UInt flag_count = 0;
UInt flag_max_count = 0;

using namespace TR;





void TR::StateX86::cpu_exception(Expt::ExceptionBase const& e)
{
    std::cerr << "Error message:" << std::endl;
    std::cerr << e << std::endl;
    UInt stack_size = sizeof(EXCEPTION_RECORD32) + sizeof(WOW64_CONTEXT);
    UInt sp_tmp = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::ESP);
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
    
    Vns eflags = z3_x86g_calculate_eflags_all(regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::CC_OP), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::CC_DEP1), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::CC_DEP2), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::CC_NDEP));
    dirty_call("putExecptionCtx32", Kc32::putExecptionCtx,
        { 
            Vns(ExceptionRecord), Vns(ContextRecord), 
            Vns(gst), eflags, 
            Vns(ExceptionCode), Vns(ExceptionAddress), Vns(ExceptionFlags),Vns(NumberParameters), Vns(nextExceptionRecord),
            Vns(info0), Vns(info1), Vns(info2) 
        },
        Ity_I32);

    regs.Ist_Put(X86_IR_OFFSET::ESP, esp - stack_size);
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


Vns TR::StateX86::get_teb()
{
    return dirty_call("x86g_use_seg_selector", x86g_use_seg_selector,
        { regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::LDT), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::GDT), regs.Iex_Get<Ity_I16>(X86_IR_OFFSET::FS).zext(16), Vns(m_ctx, 0ull) },
        Ity_I32);
}


State_Tag TR::StateX86::Ijk_call(IRJumpKind kd)
{
    switch (kd) {
    case Ijk_Sys_syscall: {
        switch (info().gguest_system()) {
        case linux:return Sys_syscall_linux();
        case windows:return Sys_syscall_windows();
        }
        return Death;
    }
    case Ijk_NoDecode: {
        //EA 09 60 47 77 33 00 00
        if (info().gguest_system() == windows) {
            if ((ULong)mem.Iex_Load<Ity_I64>(get_cpu_ip()) == 0x3377476009ea) {
                return Sys_syscall_windows();
            }
            if ((UChar)mem.Iex_Load<Ity_I8>(get_cpu_ip()) == 0xf2) {
                set_delta(1);
                return Running;
            }
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


State_Tag TR::StateX86::Sys_syscall_linux()
{
    Vns eax = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::EAX);
    Vns edi = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::EDI);
    Vns edx = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::EDX);
    Vns esi = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::ESI);
    return Death;
}

State_Tag TR::StateX86::Sys_syscall_windows()
{
    goto_ptr(vex_pop());
    Vns eax = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::EAX);
    Vns arg0 = vex_stack_get(1);
    Vns arg1 = vex_stack_get(2);
    Vns arg2 = vex_stack_get(3);
    Vns arg3 = vex_stack_get(4);
    Vns arg4 = vex_stack_get(5);


    if (eax.real()) {//这就非常的烦
        switch ((UShort)eax) {
        case 0x19: {//ntdll_NtQueryInformationProcess
            _In_      HANDLE           ProcessHandle = (HANDLE)(DWORD)arg0;
            _In_      PROCESSINFOCLASS ProcessInformationClass = (PROCESSINFOCLASS)(DWORD)arg1;
            _Out_     PVOID            ProcessInformation = (PVOID)(DWORD)arg2;
            _In_      DWORD            ProcessInformationLength = arg3;
            _Out_opt_ DWORD           ReturnLength = arg4;


            regs.Ist_Put(X86_IR_OFFSET::EAX, 0);
            return Running;
        }
        case 0x43: {
            PWOW64_CONTEXT ctx = (PWOW64_CONTEXT)(DWORD)arg0;
            Addr32 next = dirty_call("getExecptionCtx32", Kc32::getExecptionCtx, { Vns(ctx), Vns(getGSPTR()) }, Ity_I32);
            goto_ptr(next);
            regs.Ist_Put(X86_IR_OFFSET::EAX, 0);
            return Running;
        }

        }
    }
    const int df = offsetof(WOW64_CONTEXT, Esp);

    return Death;
}

















void TR::StateAMD64::cpu_exception(Expt::ExceptionBase const& e)
{
    exit(2);
}

State_Tag TR::StateAMD64::Ijk_call(IRJumpKind kd)
{
    switch (kd) {
    case Ijk_Sys_syscall: {
        switch (info().gguest_system()) {
        case linux:return Sys_syscall_linux();
        case windows:return Sys_syscall_windows();
        }
        return Death;
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
}

State_Tag StateAMD64::Sys_syscall_linux() {
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

State_Tag TR::StateAMD64::Sys_syscall_windows()
{
    return Death;
}
