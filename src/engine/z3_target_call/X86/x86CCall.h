extern "C" {
#include "guest_x86_defs.h"
}
#include "engine/variable.h"
#include "z3_target_defs.h"
Vns z3_x86g_calculate_eflags_cf(UInt cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_x86g_calculate_eflags_pf(UInt cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_x86g_calculate_eflags_af(UInt cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_x86g_calculate_eflags_zf(UInt cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_x86g_calculate_eflags_sf(UInt cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_x86g_calculate_eflags_of(UInt cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_x86g_calculate_eflags_c(Vns& cc_op, Vns& cc_dep1, Vns& cc_dep2, Vns& cc_ndep);
Vns z3_x86g_calculate_condition(Vns&/*X86Condcode*/ cond, Vns& cc_op, Vns& cc_dep1, Vns& cc_dep2, Vns& cc_ndep);
Vns z3_x86g_calculate_eflags_all(Vns& cc_op, Vns& cc_dep1, Vns& cc_dep2, Vns& cc_ndep);