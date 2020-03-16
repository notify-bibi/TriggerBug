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
    ����ĵ�һ��Ԫ�ذ�����һ����д��־����ʾ�������Υ��Ĳ������͡�
    If this value is zero, the thread attempted to read the inaccessible data.
    ������ֵΪ0����ʾ�߳���ͼ��ȡ���ɷ��ʵ����ݡ�
    If this value is 1, the thread attempted to write to an inaccessible address.
    ������ֵΪ1����ʾ�߳���ͼд�벻�ɷ��ʵĵ�ַ��
    If this value is 8, the thread causes a user-mode data execution prevention (DEP) violation.
    ������ֵ��8����ʾ�߳��߳�������һ���û�ģʽ��DEPΥ�档

    The second array element specifies the virtual address of the inaccessible data.
    ����ĵڶ���Ԫ��ָ���˲��ɷ������ݵ������ַ��



    The first element of the array contains a read-write flag that indicates the type of operation that caused the access violation.
    ����ĵ�һ��Ԫ�ذ�����һ����д��־�����ڱ�ʾ�������Υ��Ĳ������͡�
    If this value is zero, the thread attempted to read the inaccessible data.
    ���ֵΪ0����ʾ�߳���ͼ��ȡ���ɷ��ʵ����ݡ�
    If this value is 1, the thread attempted to write to an inaccessible address.
    ���ֵΪ1����ʾ�߳���ͼд�벻�ɷ��ʵĵ�ַ��
    If this value is 8, the thread causes a user-mode data execution prevention (DEP) violation.
    ���ֵΪ8����ʾ�߳�������һ���û�ģʽ��DEPΥ�档

    The second array element specifies the virtual address of the inaccessible data.
    ����ĵڶ���Ԫ��ָ���˲��ɷ������ݵ������ַ��
    The third array element specifies the underlying NTSTATUS code that resulted in the exception.
    ����ĵ�����Ԫ�ر�ʾ�ײ��NTSTATUS������ı����쳣��

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