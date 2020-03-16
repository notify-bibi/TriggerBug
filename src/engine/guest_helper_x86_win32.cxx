#include "engine/guest_helper_defs.h"
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
    UInt getExecptionCtx(IN PWOW64_CONTEXT ContextRecord,OUT VexGuestX86State* gst) {

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