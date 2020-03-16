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



UInt flag_count = 0;
UInt flag_max_count = 0;

using namespace TR;


static UInt x86g_create_mxcsr(UInt sseround)
{
    sseround &= 3;
    return 0x1F80 | (sseround << 13);
}


/*
The first element of the array contains a read-write flag that indicates the type of operation that caused the access violation.
数组的第一个元素包含了一个读写标志，表示引起访问违规的操作类型。
If this value is zero, the thread attempted to read the inaccessible data.
如果这个值为0，表示线程试图读取不可访问的数据。
If this value is 1, the thread attempted to write to an inaccessible address.
如果这个值为1，表示线程试图写入不可访问的地址。
If this value is 8, the thread causes a user-mode data execution prevention (DEP) violation.
如果这个值是8，表示线程线程引发了一个用户模式的DEP违规。

The second array element specifies the virtual address of the inaccessible data.
数组的第二个元素指定了不可访问数据的虚拟地址。



The first element of the array contains a read-write flag that indicates the type of operation that caused the access violation.
数组的第一个元素包含了一个读写标志，用于表示引起访问违规的操作类型。
If this value is zero, the thread attempted to read the inaccessible data.
如果值为0，表示线程试图读取不可访问的数据。
If this value is 1, the thread attempted to write to an inaccessible address.
如果值为1，表示线程试图写入不可访问的地址。
If this value is 8, the thread causes a user-mode data execution prevention (DEP) violation.
如果值为8，表示线程引起了一个用户模式的DEP违规。

The second array element specifies the virtual address of the inaccessible data.
数组的第二个元素指定了不可访问数据的虚拟地址。
The third array element specifies the underlying NTSTATUS code that resulted in the exception.
数组的第三个元素表示底层的NTSTATUS码引起的本次异常。

ntdll::KiUserExceptionDispatcher*/
VOID initExecptionCtx32(
    PEXCEPTION_RECORD32 ExceptionRecord, PWOW64_CONTEXT ContextRecord,
    VexGuestX86State* gst, DWORD eflags,
    DWORD ExceptionCode, DWORD ExceptionAddress, DWORD ExceptionFlags, DWORD NumberParameters, DWORD  nextExceptionRecord, 
    DWORD info0, DWORD info1, DWORD info2) {
    ExceptionRecord->ExceptionCode = ExceptionCode;
    ExceptionRecord->ExceptionFlags = ExceptionFlags;
    ExceptionRecord->ExceptionRecord = nextExceptionRecord;
    ExceptionRecord->ExceptionAddress = ExceptionAddress;
    ExceptionRecord->NumberParameters = NumberParameters;

    ExceptionRecord->ExceptionInformation[0] = info0;
    ExceptionRecord->ExceptionInformation[1] = info1;
    ExceptionRecord->ExceptionInformation[2] = info2;

    for (int i = 3; i < EXCEPTION_MAXIMUM_PARAMETERS; i++) { ExceptionRecord->ExceptionInformation[i] = 0; }



    ContextRecord->SegGs = gst->guest_GS;
    ContextRecord->SegFs = gst->guest_FS;
    ContextRecord->SegEs = gst->guest_ES;
    ContextRecord->SegDs = gst->guest_DS;

    ContextRecord->Edi = gst->guest_EDI;
    ContextRecord->Esi = gst->guest_ESI;
    ContextRecord->Ebx = gst->guest_EBX;
    ContextRecord->Edx = gst->guest_EDX;
    ContextRecord->Ecx = gst->guest_ECX;
    ContextRecord->Eax = gst->guest_EAX;

    ContextRecord->Ebp = gst->guest_EBP;
    ContextRecord->Eip = gst->guest_EIP;
    ContextRecord->SegCs = gst->guest_CS;
    
    ContextRecord->EFlags = eflags;
    ContextRecord->Esp = gst->guest_ESP;
    ContextRecord->SegSs = gst->guest_SS;


    XSAVE_FORMAT* sf = (XSAVE_FORMAT*)ContextRecord->ExtendedRegisters;
    sf->MxCsr = x86g_create_mxcsr(gst->guest_SSEROUND);
    U128* xmm = (U128*)sf->XmmRegisters;

#  define COPY_U128(_dst,_src)                       \
      do { _dst[0] = _src[0]; _dst[1] = _src[1];     \
           _dst[2] = _src[2]; _dst[3] = _src[3]; }   \
      while (0)

    COPY_U128(xmm[0], gst->guest_XMM0);
    COPY_U128(xmm[1], gst->guest_XMM1);
    COPY_U128(xmm[2], gst->guest_XMM2);
    COPY_U128(xmm[3], gst->guest_XMM3);
    COPY_U128(xmm[4], gst->guest_XMM4);
    COPY_U128(xmm[5], gst->guest_XMM5);
    COPY_U128(xmm[6], gst->guest_XMM6);
    COPY_U128(xmm[7], gst->guest_XMM7);

#  undef COPY_U128


}
//ntdll::KiUserExceptionDispatcher
VOID initExecptionCtx64(
    PEXCEPTION_RECORD64 ExceptionRecord, PCONTEXT ContextRecord,
    VexGuestAMD64State* gst, DWORD64 rflags,
    DWORD ExceptionCode, DWORD64 ExceptionAddress, DWORD ExceptionFlags, DWORD NumberParameters, DWORD64  nextExceptionRecord,
    DWORD64 info0, DWORD64 info1, DWORD64 info2) {

    ExceptionRecord->ExceptionCode = ExceptionCode;
    ExceptionRecord->ExceptionFlags = ExceptionFlags;
    ExceptionRecord->ExceptionRecord = nextExceptionRecord;
    ExceptionRecord->ExceptionAddress = ExceptionAddress;
    ExceptionRecord->NumberParameters = NumberParameters;

    ExceptionRecord->ExceptionInformation[0] = info0;
    ExceptionRecord->ExceptionInformation[1] = info1;
    ExceptionRecord->ExceptionInformation[2] = info2;
    
    for (int i = 3; i < EXCEPTION_MAXIMUM_PARAMETERS; i++) { ExceptionRecord->ExceptionInformation[i] = 0; }

    ContextRecord->MxCsr = x86g_create_mxcsr(gst->guest_SSEROUND);

    ContextRecord->SegCs = 0;
    ContextRecord->SegDs = 0;
    ContextRecord->SegEs = 0;
    ContextRecord->SegFs = gst->guest_FS_CONST;
    ContextRecord->SegGs = gst->guest_GS_CONST;
    ContextRecord->SegSs = 0;
    ContextRecord->EFlags = rflags;

    ContextRecord->Rax = gst->guest_RAX;
    ContextRecord->Rcx = gst->guest_RCX;
    ContextRecord->Rdx = gst->guest_RDX;
    ContextRecord->Rbx = gst->guest_RBX;
    ContextRecord->Rsp = gst->guest_RSP;
    ContextRecord->Rbp = gst->guest_RBP;
    ContextRecord->Rsi = gst->guest_RSI;
    ContextRecord->Rdi = gst->guest_RDI;
    ContextRecord->R8  = gst->guest_R8 ;
    ContextRecord->R9  = gst->guest_R9 ;
    ContextRecord->R10 = gst->guest_R10;
    ContextRecord->R11 = gst->guest_R11;
    ContextRecord->R12 = gst->guest_R12;
    ContextRecord->R13 = gst->guest_R13;
    ContextRecord->R14 = gst->guest_R14;
    ContextRecord->R15 = gst->guest_R15;

    ContextRecord->Rip = gst->guest_RIP;

    U256* xmm = (U256*)&ContextRecord->Xmm0;

#  define COPY_U256(_dst,_src)                       \
      do { _dst[0] = _src[0]; _dst[1] = _src[1];     \
           _dst[2] = _src[2]; _dst[3] = _src[3];     \
           _dst[4] = _src[4]; _dst[5] = _src[5];     \
           _dst[6] = _src[6]; _dst[7] = _src[7]; }   \
      while (0)

    COPY_U256(xmm[0], gst->guest_YMM0);
    COPY_U256(xmm[1], gst->guest_YMM1);
    COPY_U256(xmm[2], gst->guest_YMM2);
    COPY_U256(xmm[3], gst->guest_YMM3);
    COPY_U256(xmm[4], gst->guest_YMM4);
    COPY_U256(xmm[5], gst->guest_YMM5);
    COPY_U256(xmm[6], gst->guest_YMM6);
    COPY_U256(xmm[7], gst->guest_YMM7);

#  undef COPY_U128

}

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
        ExceptionAddress = guest_start;
        NumberParameters = 0;
        nextExceptionRecord = 0;
        info0 = 0;//error read
        info1 = e.addr();//error read addr
        info2 = 0;
    }
    case Expt::GuestMem_write_err: {
        gst = getGSPTR();
        ExceptionCode = EXCEPTION_ACCESS_VIOLATION;
        ExceptionAddress = guest_start;
        NumberParameters = 0;
        nextExceptionRecord = 0;
        info0 = 1;//write read
        info1 = e.addr();//error write addr
        info2 = 0;
    }
    case Expt::GuestRuntime_exception: {
        gst = getGSPTR();
        switch (e.jkd()) {
        case Ijk_SigTRAP:
            ExceptionCode = EXCEPTION_BREAKPOINT;
            ExceptionAddress = guest_start;
            NumberParameters = 0;
            nextExceptionRecord = 0;
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
    dirty_call("initExecptionCtx32", initExecptionCtx32,
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

    guest_start = 0x774F4200;
    set_status(Exception);

}


Vns TR::StateX86::get_teb()
{
    return dirty_call("x86g_use_seg_selector", extern_dealy_call((UChar*)x86g_use_seg_selector),
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
    { throw Expt::RuntimeIrSig(guest_start, kd); }
    default:
        vex_printf("guest address: %p jmp kind: ", guest_start);
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
    Vns eax = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::EAX);
    Vns edi = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::EDI);
    Vns edx = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::EDX);
    Vns esi = regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::ESI);

    if (eax.real()) {//这就非常的烦
        switch ((UShort)eax) {
        case 0x19: {//ntdll_NtQueryInformationProcess
            goto_ptr(vex_pop());
            return Running;
            break;
        }
        }
    }
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
    { throw Expt::RuntimeIrSig(guest_start, kd); }
    default:
        vex_printf("guest address: %p . error jmp kind: ", guest_start);
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
