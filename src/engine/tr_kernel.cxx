
//#undef _DEBUG


#include "instopt/engine/tr_kernel.h"
#include "instopt/helper/z3_target_call.h"

#include <Windows.h>
#include <winternl.h>
extern "C" {
#include "../valgrind-3.17.0/VEX/priv/guest_amd64_defs.h"
#include "../valgrind-3.17.0/VEX/priv/guest_arm64_defs.h"
#include "../valgrind-3.17.0/VEX/priv/guest_arm_defs.h"
#include "../valgrind-3.17.0/VEX/priv/guest_mips_defs.h"
#include "../valgrind-3.17.0/VEX/priv/guest_nanomips_defs.h"
#include "../valgrind-3.17.0/VEX/priv/guest_ppc_defs.h"
#include "../valgrind-3.17.0/VEX/priv/guest_x86_defs.h"
#include "../valgrind-3.17.0/VEX/priv/ir_opt.h"
};


#define KE_WINDOWS_ENABLE
//#define KE_LINUX_ENABLE
//#define KE_DARWIND_ENABLE
/*
linux
https://chromium.googlesource.com/chromiumos/docs/+/master/constants/syscalls.md
https://github.com/torvalds/linux/blob/master/arch/x86/entry/entry_64_compat.S
http://www.o3one.org/hwdocs/amd64bit/x86-64_overview.pdf

arch	syscall NR	return	arg0	arg1	arg2	arg3	arg4	arg5
arm	    r7	        r0	    r0	    r1	    r2	    r3	    r4	    r5
arm64	x8	        x0	    x0	    x1	    x2	    x3	    x4	    x5
x86	    eax	        eax	    ebx	    ecx	    edx	    esi	    edi	    ebp
x86_64	rax	        rax	    rdi   	rsi	    rdx	    r10	    r8	    r9


*/

namespace Ke {
    class OS_Unknow : public Kernel {
    public:
        OS_Unknow() : Kernel(OS_Kernel_Kd::OSK_Unknow) {}


        virtual TR::State_Tag Ijk_call(TR::State& st, IRJumpKind kd) override;
        virtual void cpu_exception(TR::State& st, Expt::ExceptionBase const& e) override;
        virtual void avoid_anti_debugging(TR::State& st) override {};

        virtual ~OS_Unknow() {}
    };

    TR::State_Tag OS_Unknow::Ijk_call(TR::State& st, IRJumpKind kd)
    {
        switch (kd) {
        case Ijk_Sys_syscall: {

            break;
        }
        case Ijk_NoDecode: {
            st.logger->critical("Error message: valgrind Ijk_NoDecode 0x{:x}", st.get_cpu_ip());
            return TR::NoDecode;
        }
        case Ijk_SigILL:         /* current instruction synths SIGILL */
        case Ijk_SigTRAP:        /* current instruction synths SIGTRAP */
        case Ijk_SigSEGV:        /* current instruction synths SIGSEGV */
        case Ijk_SigBUS:         /* current instruction synths SIGBUS */
        case Ijk_SigFPE:         /* current instruction synths generic SIGFPE */
        case Ijk_SigFPE_IntDiv:  /* current instruction synths SIGFPE - IntDiv */
        case Ijk_SigFPE_IntOvf:  /* current instruction synths SIGFPE - IntOvf */
        { throw Expt::RuntimeIrSig(st.get_cpu_ip(), kd); }
        default:
            st.logger->warn("guest address: 0x{x} jmp kind: {}", st.get_cpu_ip(), kd);
        };
        return TR::State_Tag::Death;
    };

    void OS_Unknow::cpu_exception(TR::State& st, Expt::ExceptionBase const& e)
    {
    }
    ;
};


#ifdef KE_WINDOWS_ENABLE
// Windows
#include <Windows.h>


static UInt x86g_create_mxcsr(UInt sseround)
{
    sseround &= 3;
    return 0x1F80 | (sseround << 13);
}

static UInt x86g_create_sseround(UInt mxcsr)
{
    return (mxcsr >> 13) & 3;
}

namespace Kc32 {

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

    VOID putExecptionCtx(
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
        __m128i* xmm = (__m128i*)sf->XmmRegisters;

#  define COPY_U128(_dst,_src) _dst = *(__m128i*)_src
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


    //ntdll::ntdll_NtContinue
    UInt getExecptionCtx(IN PWOW64_CONTEXT ContextRecord, OUT VexGuestX86State* gst) {

        gst->guest_GS = ContextRecord->SegGs;
        gst->guest_FS = ContextRecord->SegFs;
        gst->guest_ES = ContextRecord->SegEs;
        gst->guest_DS = ContextRecord->SegDs;

        gst->guest_EDI = ContextRecord->Edi;
        gst->guest_ESI = ContextRecord->Esi;
        gst->guest_EBX = ContextRecord->Ebx;
        gst->guest_EDX = ContextRecord->Edx;
        gst->guest_ECX = ContextRecord->Ecx;
        gst->guest_EAX = ContextRecord->Eax;

        gst->guest_EBP = ContextRecord->Ebp;
        gst->guest_EIP = ContextRecord->Eip;
        gst->guest_CS = ContextRecord->SegCs;

        //eflags = ContextRecord->EFlags;
        gst->guest_ESP = ContextRecord->Esp;
        gst->guest_SS = ContextRecord->SegSs;


        XSAVE_FORMAT* sf = (XSAVE_FORMAT*)ContextRecord->ExtendedRegisters;
        gst->guest_SSEROUND = x86g_create_sseround(sf->MxCsr);
        __m128i* xmm = (__m128i*)sf->XmmRegisters;

#  define COPY_U128(_dst,_src) *(__m128i*)_dst = _src
        COPY_U128(gst->guest_XMM0, xmm[0]);
        COPY_U128(gst->guest_XMM1, xmm[1]);
        COPY_U128(gst->guest_XMM2, xmm[2]);
        COPY_U128(gst->guest_XMM3, xmm[3]);
        COPY_U128(gst->guest_XMM4, xmm[4]);
        COPY_U128(gst->guest_XMM5, xmm[5]);
        COPY_U128(gst->guest_XMM6, xmm[6]);
        COPY_U128(gst->guest_XMM7, xmm[7]);
#  undef COPY_U128

        return gst->guest_EIP;
    }
};

namespace Ke {

	class Windows : public Kernel {
        
	public:
        Windows(): Kernel(OS_Kernel_Kd::OSK_Windows) {}
        virtual ~Windows(){}

        TR::State_Tag Sys_syscall(TR::State& st);
		virtual TR::State_Tag Ijk_call(TR::State& st, IRJumpKind kd) override;
		virtual void cpu_exception(TR::State& st, Expt::ExceptionBase const& e) override;
        virtual void avoid_anti_debugging(TR::State& st) override;

        Addr64 get_TEB_p64(TR::State& st);
        Addr32 get_TEB_p32(TR::State& st);
        void cpu_exception_32(TR::State& st, Expt::ExceptionBase const& e);
        void cpu_exception_64(TR::State& st, Expt::ExceptionBase const& e);
	};



    TR::State_Tag Windows::Sys_syscall(TR::State& st)
    {
        decltype(st.regs)& regs = st.regs;
        decltype(st.mem)& mem = st.mem;
        z3::vcontext& ctx = st.ctx();

        
        auto eax = regs.get<Ity_I32>(AMD64_IR_OFFSET::RAX);
        // mov     r10, rcx
        auto arg0 = regs.get<Ity_I64>(AMD64_IR_OFFSET::R10);
        auto arg1 = regs.get<Ity_I64>(AMD64_IR_OFFSET::RDX);
        auto arg2 = regs.get<Ity_I64>(AMD64_IR_OFFSET::R8);
        auto arg3 = regs.get<Ity_I64>(AMD64_IR_OFFSET::R9);

        auto arg4 = st.vex_stack_get<ULong>(5);
        auto arg5 = st.vex_stack_get<ULong>(6);
        auto arg6 = st.vex_stack_get<ULong>(7);


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

                UInt BaseAddress = st.mem.load<Ity_I32>(arg1).tor();
                UInt RegionSize = st.mem.load<Ity_I32>(arg3).tor();
                st.mem.map(BaseAddress, RegionSize);
                st.logger->info("ntdll_NtAllocateVirtualMemory map(e a :0x{:x} sz : 0x{:x})", BaseAddress, RegionSize);

                regs.set(X86_IR_OFFSET::EAX, 0);
                return TR::Running;
            }
            case 0x19: {//ntdll_NtQueryInformationProcess
                _In_      HANDLE           ProcessHandle = (HANDLE)(size_t)(DWORD)arg0.tor();
                _In_      PROCESSINFOCLASS ProcessInformationClass = (PROCESSINFOCLASS)(DWORD)arg1.tor();
                _Out_     PVOID            ProcessInformation = (PVOID)(size_t)(DWORD)arg2.tor();
                _In_      DWORD            ProcessInformationLength = arg3.tor();
                _Out_opt_ DWORD            ReturnLength = arg4.tor();

                if (ProcessInformationClass == ProcessDebugPort) {//kernelbase_CheckRemoteDebuggerPresent
                    st.mem.store((Addr32)(ULong)ProcessInformation, 0);
                    st.logger->info("war: ntdll_NtQueryInformationProcess(,,ProcessDebugPort,) hide");

                }
                if (ProcessInformationClass == 37) {//

                }
                regs.set(X86_IR_OFFSET::EAX, 0);
                return TR::Running;
            }
            case 0x23: { // ntdll_ZwQueryVirtualMemory 遍历进程模块
                break;
            }
            case 0x25: { // ntdll_ZwQueryInformationThread
                break;
            }
            case 0x43: { // ntdll_NtContinue
                auto wow64_ctx = arg0; // PWOW64_CONTEXT
                auto next = st.dirty_call("getExecptionCtx32", Kc32::getExecptionCtx, { wow64_ctx, rsval<Addr64>(ctx, st.getGSPTR()) }, Ity_I32);
                vassert(next.real());
                st.goto_ptr(next);
                regs.set(X86_IR_OFFSET::EAX, 0);
                return TR::Running;
            }
            case 0x50: { // ntdll_NtProtectVirtualMemory
                /*
                IN HANDLE               ProcessHandle,
                IN OUT PVOID            *BaseAddress,
                IN OUT PULONG           NumberOfBytesToProtect,
                IN ULONG                NewAccessProtection,
                OUT PULONG              OldAccessProtection 
                */

                /*ProcessHandle*/ HANDLE ProcessHandle = arg0.tor();
                if (ProcessHandle == (HANDLE)(-1)) {
                    /*BaseAddress*/ 
                    st.mem.store(arg1, 0x401000ull);
                    /*NumberOfBytesToProtect*/ 
                    st.mem.store(arg2, 0x164000ull);
                    ULONG NewAccessProtection = arg3.tor();
                    st.mem.store(arg4, 0x40ull);
                }
                regs.set(X86_IR_OFFSET::EAX, 0);
                return TR::Running;
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


                rsval<Long> count = st.vctx().get_hook_read()(st, arg5, arg6);
                st.mem.store(arg4, 0ull);
                st.mem.store(arg4 + 8, count);
                regs.set(X86_IR_OFFSET::EAX, 1);
                return TR::Running;
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

                st.vctx().get_hook_write()(st, arg5, arg6);
                st.mem.store(arg4, 0);
                st.mem.store(arg4 + 8, arg6);
                regs.set(X86_IR_OFFSET::EAX, 0);
                return TR::Running;
            }
            case 0x01b0007: {//ntdll_NtDeviceIoControlFile


                regs.set(X86_IR_OFFSET::EAX, 0);
                return TR::Running;
            }
            }

        }
        st.logger->critical("ip ea:0x{:x} : Sys_syscall_windows(id:0x{:} arg0:{} arg1:{} arg2:{} arg3:{} arg4:{} arg5:{}) not define", st.get_cpu_ip(), eax.str(), arg0.str(), arg1.str(), arg2.str(), arg3.str(), arg4.str(), arg5.str());
        /*std::cerr << "Invok Stack :\n" << (std::string)st.get_InvokStack() << std::endl;*/
        return TR::Death;
    };




	TR::State_Tag Windows::Ijk_call(TR::State& st, IRJumpKind kd)
	{
		switch (kd) {
		case Ijk_Sys_syscall: {
            return Sys_syscall(st);
		}
        case Ijk_Sys_int32: {
            UShort cs = (UShort)st.regs.get<Ity_I16>(AMD64_IR_OFFSET::CS).tor();
            st.x86_set_mode(cs);
            return TR::Running;
        }
		case Ijk_NoDecode: {
            // 77736000 ea096073773300  jmp     0033:77736009
			if ((UChar)st.mem.load<Ity_I8>(st.get_cpu_ip()).tor() == 0xea) {
                Addr64 ptr = (Addr64)st.mem.load<Ity_I32>(st.get_cpu_ip() + 1).tor();
                UShort cs = (UShort)st.mem.load<Ity_I32>(st.get_cpu_ip() + 1 + 4).tor();
                st.x86_set_mode(cs); // amd64
                st.set_delta(ptr - st.get_cpu_ip());
                return TR::Running;
			}
			if ((UChar)st.mem.load<Ity_I8>(st.get_cpu_ip()).tor() == 0xf2) {
                st.set_delta(1);
				return TR::Running;
			}
            st.logger->critical("Error message: valgrind Ijk_NoDecode 0x{:x}", st.get_cpu_ip());
			return TR::NoDecode;
		}
		case Ijk_SigILL:         /* current instruction synths SIGILL */
		case Ijk_SigTRAP:        /* current instruction synths SIGTRAP */
		case Ijk_SigSEGV:        /* current instruction synths SIGSEGV */
		case Ijk_SigBUS:         /* current instruction synths SIGBUS */
		case Ijk_SigFPE:         /* current instruction synths generic SIGFPE */
		case Ijk_SigFPE_IntDiv:  /* current instruction synths SIGFPE - IntDiv */
		case Ijk_SigFPE_IntOvf:  /* current instruction synths SIGFPE - IntOvf */
		{ throw Expt::RuntimeIrSig(st.get_cpu_ip(), kd); }
		default:
            st.logger->warn("guest address: 0x{:x} jmp kind: {}", st.get_cpu_ip(), kd);
            spdlog::warn("guest address: 0x{:x} jmp kind: {}", st.get_cpu_ip(), kd);
		}
		return TR::Death;
	}


    void Windows::cpu_exception(TR::State& st, Expt::ExceptionBase const& e)
    {
        if (st.vinfo().is_mode_32()) {
            cpu_exception_32(st, e);
        }
        else {
            cpu_exception_64(st, e);
        }
    }

	

    void Windows::cpu_exception_32(TR::State& st, Expt::ExceptionBase const& e)
    {
        decltype(st.regs)& regs = st.regs;
        decltype(st.mem)& mem = st.mem;
        z3::vcontext& ctx = st.ctx();

        UInt stack_size = sizeof(EXCEPTION_RECORD32) + sizeof(WOW64_CONTEXT);
        UInt sp_tmp = regs.get<Ity_I32>(X86_IR_OFFSET::ESP).tor();
        UInt esp = sp_tmp - 532;


        PWOW64_CONTEXT ContextRecord = (PWOW64_CONTEXT)(esp - sizeof(WOW64_CONTEXT));
        PEXCEPTION_RECORD32 ExceptionRecord = (PEXCEPTION_RECORD32)(esp - sizeof(WOW64_CONTEXT) - sizeof(EXCEPTION_RECORD32));
        Addr64 gst = st.getGSPTR();
        DWORD ExceptionCode, ExceptionAddress, ExceptionFlags, NumberParameters, nextExceptionRecord;
        DWORD info0, info1, info2;

        switch (e.errTag()) {
        case Expt::GuestMem_read_err: {
            //gst = getGSPTR();
            ExceptionCode = EXCEPTION_ACCESS_VIOLATION;
            ExceptionAddress = st.get_cpu_ip();
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
            ExceptionAddress = st.get_cpu_ip();
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
                ExceptionAddress = st.get_cpu_ip();
                NumberParameters = 0;
                nextExceptionRecord = 0;
                ExceptionFlags = 0;
                info0 = 0;
                info1 = 0;
                info2 = 0;
                break;
            default:
                st.set_status(TR::Death);
                return;
            }
            break;
        }
        default:
            st.set_status(TR::Death);
            return;
        }


        std::cout << " SEH Exception ID:[" << std::hex << ExceptionCode << "] at:" << std::hex << st.get_cpu_ip() << std::endl;

        auto eflags = z3_x86g_calculate_eflags_all(regs.get<Ity_I32>(X86_IR_OFFSET::CC_OP), regs.get<Ity_I32>(X86_IR_OFFSET::CC_DEP1), regs.get<Ity_I32>(X86_IR_OFFSET::CC_DEP2), regs.get<Ity_I32>(X86_IR_OFFSET::CC_NDEP));


        mem.map(0x100000, 99999);


        st.dirty_call("putExecptionCtx32", Kc32::putExecptionCtx,
            {
                rcval<Addr32>(ctx, (size_t)ExceptionRecord), rcval<Addr32>(ctx, (size_t)ContextRecord),
                rcval<Addr64>(ctx, gst), eflags,
                rcval<int>(ctx, ExceptionCode), rcval<Addr32>(ctx, ExceptionAddress), rcval<int>(ctx, ExceptionFlags),rcval<int>(ctx, NumberParameters), rcval<Addr32>(ctx, nextExceptionRecord),
                rcval<Addr32>(ctx, info0), rcval<Addr32>(ctx, info1), rcval<Addr32>(ctx, info2)
            },
            Ity_I32);

        regs.set(X86_IR_OFFSET::ESP, esp - stack_size);
        st.vex_push_const((Addr32)(ULong)ContextRecord);
        st.vex_push_const((Addr32)(ULong)ExceptionRecord);

        Addr32 ntdll_KiUserExceptionDispatcher = (Addr32)param().get("ntdll_KiUserExceptionDispatcher");
        if (!ntdll_KiUserExceptionDispatcher) {
            st.logger->warn("(ctx32).param().set(\"ntdll_KiUserExceptionDispatcher\", 0x-----);");
            st.set_status(TR::Death);
            return;
        }
        else {
            st.goto_ptr(ntdll_KiUserExceptionDispatcher);
            st.set_status(TR::Exception);
        }

    }


    void Windows::cpu_exception_64(TR::State& st, Expt::ExceptionBase const& e) {}

    void Windows::avoid_anti_debugging(TR::State& st)
    {
        decltype(st.regs)& regs = st.regs;
        decltype(st.mem)& mem = st.mem;
        z3::vcontext& ctx = st.ctx();
        // kernelbase_IsDebuggerPresent
        auto peb = mem.load<Ity_I32>(get_TEB_p32(st) + 0x30);
        if (peb.real()) {
            UChar v = mem.load<Ity_I8>(peb + 2).tor();
            if (v) {
                spdlog::info("hide kernelbase_IsDebuggerPresent");
                mem.store(peb + 2, (UChar)0);
            }
            //PEB.NtGlobalFlag
            v = mem.load<Ity_I8>(peb + 0x68).tor();
            if (v == 0x70) {
                spdlog::info("hide PEB.NtGlobalFlag");
                mem.store(peb + 0x68, (UChar)0);
            }
            //patch PEB.ProcessHeap.Flags/ForceFlags
            auto process_heap = mem.load<Ity_I32>(peb + 0x18);
            v = mem.load<Ity_I8>(process_heap + 0xc).tor();
            if (v != 2) {
                spdlog::info("hide PEB.ProcessHeap.Flags");
                mem.store(process_heap + 0xc, 2);
            }
            v = mem.load<Ity_I8>(process_heap + 0x10).tor();
            if (v != 0) {
                spdlog::info("hide PEB.ProcessHeap.ForceFlags");
                mem.store(process_heap + 0x10, 0);
            }
        }
    }

    Addr32 Windows::get_TEB_p32(TR::State& st)
    {
        return st.dirty_call("x86g_use_seg_selector", x86g_use_seg_selector,
                    { 
                        st.regs.get<Ity_I64>(X86_IR_OFFSET::LDT),
                        st.regs.get<Ity_I64>(X86_IR_OFFSET::GDT),
                        st.regs.get<Ity_I16>(X86_IR_OFFSET::FS),
                        rcval<Addr32>(st.ctx(), (ULong)0)
                    },
                    Ity_I32).tors<false, 32>().tor();
    }


};
#endif // KE_WINDOWS_ENABLE


#ifdef KE_LINUX_ENABLE
// Linux
namespace Ke {
    /*
    eax	系统调用号
    ebx	第一个参数
    ecx	第二个参数
    edx	第三个参数
    esi	第四个参数
    edi	第五个参数

    rdi	第一个参数
    rsi	第二个参数
    rdx	第三个参数
    r10	第四个参数
    r8	第五个参数
    r9	第六个参数
    */
	class Linux : public Ke::Kernel {
        ULong m_g_brk = ALIGN(0x0000000000603000, 64);
	public:
        Linux(TR::StateBase& s) : Ke::Kernel(OS_Kernel_Kd::OSK_Linux, s) {}
        Linux(TR::StateBase& fs, TR::StateBase& s) : Kernel(OS_Kernel_Kd::OSK_Linux, s, fs.get_kernel()) {}


        virtual TR::State_Tag Ijk_call(IRJumpKind kd) override;
        virtual void cpu_exception(Expt::ExceptionBase const& e) override;
        virtual void avoid_anti_debugging() override;

        TR::State_Tag Ijk_call_32(IRJumpKind kd);
        TR::State_Tag Sys_syscall_32();
        void cpu_exception_32(Expt::ExceptionBase const& e);
        void avoid_anti_debugging_32();
        Addr32 get_TEB_p32();

        TR::State_Tag Ijk_call_64(IRJumpKind kd);
        TR::State_Tag Sys_syscall_64();
        void cpu_exception_64(Expt::ExceptionBase const& e);
        void avoid_anti_debugging_64();
        Addr64 get_TEB_p64();
	};



    TR::State_Tag Linux::Ijk_call(IRJumpKind kd)
    {
        return TR::State_Tag();
    }

    void Linux::cpu_exception(Expt::ExceptionBase const& e)
    {
    }

    void Linux::avoid_anti_debugging()
    {
    }

    TR::State_Tag Linux::Ijk_call_32(IRJumpKind kd)
    {
        switch (kd) {
        case Ijk_Sys_syscall: {
            return Sys_syscall_32(se);
        }
        case Ijk_NoDecode: {
            std::cerr << "Error message: valgrind Ijk_NoDecode " << std::hex << st.get_cpu_ip() << std::endl;
            return TR::NoDecode;
        }
        case Ijk_SigILL:         /* current instruction synths SIGILL */
        case Ijk_SigTRAP:        /* current instruction synths SIGTRAP */
        case Ijk_SigSEGV:        /* current instruction synths SIGSEGV */
        case Ijk_SigBUS:         /* current instruction synths SIGBUS */
        case Ijk_SigFPE:         /* current instruction synths generic SIGFPE */
        case Ijk_SigFPE_IntDiv:  /* current instruction synths SIGFPE - IntDiv */
        case Ijk_SigFPE_IntOvf:  /* current instruction synths SIGFPE - IntOvf */
        { throw Expt::RuntimeIrSig(st.get_cpu_ip(), kd); }
        default:
            vex_printf("guest address: %p . error jmp kind: ", st.get_cpu_ip());
            ppIRJumpKind(kd);
            vex_printf("\n");
        }
    }

    TR::State_Tag Linux::Sys_syscall_32()
    {
        decltype(st.regs)& regs = st.regs;
        decltype(st.mem)& mem = st.mem;
        TR::vex_context& vctx = se.vctx();
        z3::vcontext& ctx = st.ctx();
        auto eax = regs.get<Ity_I32>(X86_IR_OFFSET::EAX);
        auto edi = regs.get<Ity_I32>(X86_IR_OFFSET::EDI);
        auto edx = regs.get<Ity_I32>(X86_IR_OFFSET::EDX);
        auto esi = regs.get<Ity_I32>(X86_IR_OFFSET::ESI);
        return TR::Death;
    }

    void Linux::cpu_exception_32(Expt::ExceptionBase const& e)
    {
    }

    void Linux::avoid_anti_debugging_32()
    {
    }

    Addr32 Linux::get_TEB_p32()
    {
        return Addr32();
    }

    TR::State_Tag Linux::Ijk_call_64(IRJumpKind kd)
    {

        switch (kd) {
        case Ijk_Sys_syscall: {
            return Sys_syscall_64(se);
        }
        case Ijk_NoDecode: {
            std::cerr << "Error message:" << std::hex << st.get_cpu_ip() << std::endl;
            return TR::NoDecode;
        }
        case Ijk_SigILL:         /* current instruction synths SIGILL */
        case Ijk_SigTRAP:        /* current instruction synths SIGTRAP */
        case Ijk_SigSEGV:        /* current instruction synths SIGSEGV */
        case Ijk_SigBUS:         /* current instruction synths SIGBUS */
        case Ijk_SigFPE:         /* current instruction synths generic SIGFPE */
        case Ijk_SigFPE_IntDiv:  /* current instruction synths SIGFPE - IntDiv */
        case Ijk_SigFPE_IntOvf:  /* current instruction synths SIGFPE - IntOvf */
        { throw Expt::RuntimeIrSig(st.get_cpu_ip(), kd); }
        default:
            vex_printf("guest address: %p . error jmp kind: ", st.get_cpu_ip());
            ppIRJumpKind(kd);
            vex_printf("\n");
        }
        return TR::Death;
    }

    TR::State_Tag Linux::Sys_syscall_64()
    {
        decltype(st.regs)& regs = st.regs;
        decltype(st.mem)& mem = st.mem;
        TR::vex_context& vctx = se.vctx();
        z3::vcontext& ctx = st.ctx();
        auto rdi = regs.get<Ity_I64>(AMD64_IR_OFFSET::RDI);
        auto rsi = regs.get<Ity_I64>(AMD64_IR_OFFSET::RSI);
        auto rdx = regs.get<Ity_I64>(AMD64_IR_OFFSET::RDX);

        auto al = regs.get<Ity_I8>(AMD64_IR_OFFSET::RAX);
        if (al.real()) {
            switch ((UChar)al.tor()) {
            case 0:// //LINUX - sys_read
                if (rdi.tor() == 0) {
                    rsval<Addr64> count = vctx.get_hook_read()(st, rsi, rdx).tors<false, 64>();
                    regs.set(AMD64_IR_OFFSET::RAX, count);
                    return TR::Running;
                }
            case 1: {//LINUX - sys_write
                vctx.get_hook_write()(st, rsi, rdx);
                regs.set(AMD64_IR_OFFSET::RAX, rdx);
                return TR::Running;
            }

            case 0x3: {//LINUX - sys_close
                vex_printf("system call: sys_close description:0x%x\n", (ULong)rdi.tor());
                regs.set(AMD64_IR_OFFSET::RAX, 1);
                break;
            }
            case 0x5: {//LINUX - sys_newfstat
                vex_printf("system call: sys_newfstat\tfd:0x%x 	struct stat __user *statbuf:0x%x", (ULong)rdi.tor(), (ULong)rsi.tor());
                regs.set(AMD64_IR_OFFSET::RAX, 0ull);
                return TR::Running;
            }

            case 0xC: {//LINUX - sys_brk
                ULong rbx = regs.get<Ity_I64>(AMD64_IR_OFFSET::RBX).tor();
                vex_printf("system call: brk address:0x%x\n", rbx);
                ULong brk = rbx;
                if (brk) {
                    if (brk < m_g_brk) {
                        mem.unmap(brk, m_g_brk);
                        m_g_brk = ALIGN(brk, 32);
                    }
                    else if (brk == m_g_brk) {
                        mem.map(m_g_brk, m_g_brk + 0x21000);
                        m_g_brk = ALIGN(m_g_brk + 0x21000, 32);
                    }
                    else {
                        mem.map(m_g_brk, brk);
                        m_g_brk = ALIGN(brk, 32);
                    }
                }
                regs.set(AMD64_IR_OFFSET::RAX, m_g_brk);
                return TR::Running;
            }
            case 0x23: {//LINUX - sys_nanosleep
                vex_printf("system call: sys_nanosleep\n");
                return TR::Running;
            }
            case 0xE7: {//LINUX - sys_Exit
                vex_printf("system call: sys_Exit\n");
                return TR::Exit;
            }
            case 0x101: {//LINUX - sync_file_range
                // rsi filename   rdx flag
                std::stringstream filename;
                if (rsi.real()) {
                    UInt p = st.getStr(filename, rsi.tor());
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

        return TR::Death;
    }

    void Linux::cpu_exception_64(Expt::ExceptionBase const& e)
    {
    }

    void Linux::avoid_anti_debugging_64()
    {
    }

    Addr64 Linux::get_TEB_p64()
    {
        return Addr64();
    }

};

#endif // KE_LINUX_ENABLE

#ifdef KE_DARWIND_ENABLE
// Darwin
namespace Ke {

    class Darwin : public Ke::Kernel {
    public:
        Darwin(TR::StateBase& s) : Ke::Kernel(OS_Kernel_Kd::OSK_Darwin, s) {}
        Darwin(TR::StateBase& fs, TR::StateBase& s) : Kernel(OS_Kernel_Kd::OSK_Darwin, s, fs.get_kernel()) {}


        virtual TR::State_Tag Ijk_call(IRJumpKind kd) override;
        virtual void cpu_exception(Expt::ExceptionBase const& e) override;
        virtual void avoid_anti_debugging() override;

        TR::State_Tag Ijk_call_32(IRJumpKind kd);
        TR::State_Tag Sys_syscall_32();
        void cpu_exception_32(Expt::ExceptionBase const& e);
        void avoid_anti_debugging_32();
        Addr32 get_TEB_p32();

        TR::State_Tag Ijk_call_64(IRJumpKind kd);
        TR::State_Tag Sys_syscall_64();
        void cpu_exception_64(Expt::ExceptionBase const& e);
        void avoid_anti_debugging_64();
        Addr64 get_TEB_p64();
    };

    TR::State_Tag Darwin::Ijk_call(IRJumpKind kd)
    {
        return TR::State_Tag();
    }

    void Darwin::cpu_exception(Expt::ExceptionBase const& e)
    {
    }

    void Darwin::avoid_anti_debugging()
    {
    }

    TR::State_Tag Darwin::Ijk_call_32(IRJumpKind kd)
    {
        return TR::State_Tag();
    }

    TR::State_Tag Darwin::Sys_syscall_32()
    {
        return TR::State_Tag();
    }

    void Darwin::cpu_exception_32(Expt::ExceptionBase const& e)
    {
    }

    void Darwin::avoid_anti_debugging_32()
    {
    }

    Addr32 Darwin::get_TEB_p32()
    {
        return Addr32();
    }

    TR::State_Tag Darwin::Ijk_call_64(IRJumpKind kd)
    {
        return TR::State_Tag();
    }

    TR::State_Tag Darwin::Sys_syscall_64()
    {
        return TR::State_Tag();
    }

    void Darwin::cpu_exception_64(Expt::ExceptionBase const& e)
    {
    }

    void Darwin::avoid_anti_debugging_64()
    {
    }

    Addr64 Darwin::get_TEB_p64()
    {
        return Addr64();
    }

};
#endif // KE_DARWIND_ENABLE


class kernel_v : public TR::sys_params_value {
public:
    kernel_v(Ke::Kernel* k) :sys_params_value((size_t)k) {
        

    }
    ~kernel_v() {
        Ke::Kernel* k = (Ke::Kernel*)value();
        delete k;
    }
};


namespace TR {
    std::shared_ptr<TR::sys_params_value> gen_kernel(Ke::OS_Kernel_Kd kd) {
        switch (kd)
        {
#ifdef KE_WINDOWS_ENABLE
        case Ke::OS_Kernel_Kd::OSK_Windows: return std::make_shared<kernel_v>(new Ke::Windows); break;
#endif
#ifdef KE_LINUX_ENABLE
        case Ke::OS_Kernel_Kd::OSK_Linux: m_kernel = std::make_shared<kernel_v>(new Ke::Linux); break;
#endif
#ifdef KE_DARWIN_ENABLE
        case Ke::OS_Kernel_Kd::OSK_Darwin:m_kernel = std::make_shared<kernel_v>(new Ke::Darwin); break;
#endif
        default: // Ke::OS_Kernel_Kd::OSK_Unknow
                return std::make_shared<kernel_v>(new Ke::OS_Unknow); break;
            }
    };




};