#include "engine/guest_helper_defs.h"



static UInt x86g_create_mxcsr(UInt sseround)
{
    sseround &= 3;
    return 0x1F80 | (sseround << 13);
}


namespace Kc64 {
    //ntdll::KiUserExceptionDispatcher
    VOID putExecptionCtx(
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
        ContextRecord->R8 = gst->guest_R8;
        ContextRecord->R9 = gst->guest_R9;
        ContextRecord->R10 = gst->guest_R10;
        ContextRecord->R11 = gst->guest_R11;
        ContextRecord->R12 = gst->guest_R12;
        ContextRecord->R13 = gst->guest_R13;
        ContextRecord->R14 = gst->guest_R14;
        ContextRecord->R15 = gst->guest_R15;

        ContextRecord->Rip = gst->guest_RIP;

        __m256i* xmm = (__m256i*) & ContextRecord->Xmm0;


#  define COPY_U256(_dst,_src) _dst = *(__m256i*)_src
        COPY_U256(xmm[0], gst->guest_YMM0);
        COPY_U256(xmm[1], gst->guest_YMM1);
        COPY_U256(xmm[2], gst->guest_YMM2);
        COPY_U256(xmm[3], gst->guest_YMM3);
        COPY_U256(xmm[4], gst->guest_YMM4);
        COPY_U256(xmm[5], gst->guest_YMM5);
        COPY_U256(xmm[6], gst->guest_YMM6);
        COPY_U256(xmm[7], gst->guest_YMM7);
#  undef COPY_U256

    }



}