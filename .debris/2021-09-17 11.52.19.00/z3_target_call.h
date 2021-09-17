//AMD64:
// #include "engine/variable.h"
extern "C" ULong x86g_use_seg_selector(HWord ldt, HWord gdt, UInt seg_selector, UInt virtual_addr);
UChar* extern_dealy_call(UChar* fuc);

//0xd127ca11 = dirty call
#define DIRTY_CALL_MAGIC ((UChar*) 0xd127ca11)

#include "instopt/helper/AMD64/amd64CCall.h"
#include "instopt/helper/X86/x86CCall.h"

void* funcDict(void*);
void Func_Map_Init();