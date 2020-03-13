//AMD64:
#include "engine/variable.h"
extern "C" ULong x86g_use_seg_selector(HWord ldt, HWord gdt, UInt seg_selector, UInt virtual_addr);
UChar* extern_dealy_call(UChar* fuc);

//0xd127ca11 = dirty call
#define DIRTY_CALL_MAGIC ((UChar*) 0xd127ca11)

Vns z3_amd64g_calculate_condition(Vns/*AMD64Condcode*/& cond,
    Vns& cc_op,
    Vns& cc_dep1,
    Vns& cc_dep2,
    Vns& cc_ndep);


Vns z3_amd64g_calculate_rflags_c(Vns& cc_op,
    Vns& cc_dep1,
    Vns& cc_dep2,
    Vns& cc_ndep);


Vns z3_amd64g_calculate_rflags_all(Vns& cc_op,
    Vns& cc_dep1,
    Vns& cc_dep2,
    Vns& cc_ndep);

//X86:
Vns z3_x86g_calculate_eflags_c(Vns& cc_op,
    Vns& cc_dep1,
    Vns& cc_dep2,
    Vns& cc_ndep);

Vns z3_x86g_calculate_condition(
    Vns&/*X86Condcode*/ cond,
    Vns& cc_op,
    Vns& cc_dep1,
    Vns& cc_dep2,
    Vns& cc_ndep);

Vns z3_x86g_calculate_eflags_all(Vns& cc_op,
    Vns& cc_dep1,
    Vns& cc_dep2,
    Vns& cc_ndep);

void* funcDict(void*);
void Func_Map_Init();