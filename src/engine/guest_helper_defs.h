#ifndef _GUEST_HELPER_DEFS_
#define _GUEST_HELPER_DEFS_
#include "engine.h"
#include <Windows.h>

namespace Kc32 {
    VOID putExecptionCtx(
        PEXCEPTION_RECORD32 ExceptionRecord, PWOW64_CONTEXT ContextRecord,
        VexGuestX86State* gst, DWORD eflags,
        DWORD ExceptionCode, DWORD ExceptionAddress, DWORD ExceptionFlags, DWORD NumberParameters, DWORD  nextExceptionRecord,
        DWORD info0, DWORD info1, DWORD info2);
    UInt getExecptionCtx(IN PWOW64_CONTEXT ContextRecord, OUT VexGuestX86State* gst);
};

namespace Kc64 {

    VOID putExecptionCtx(
        PEXCEPTION_RECORD64 ExceptionRecord, PCONTEXT ContextRecord,
        VexGuestAMD64State* gst, DWORD64 rflags,
        DWORD ExceptionCode, DWORD64 ExceptionAddress, DWORD ExceptionFlags, DWORD NumberParameters, DWORD64  nextExceptionRecord,
        DWORD64 info0, DWORD64 info1, DWORD64 info2);
};
#endif // !_GUEST_HELPER_DEFS_
