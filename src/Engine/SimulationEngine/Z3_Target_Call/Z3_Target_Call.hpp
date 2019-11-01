//AMD64:
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