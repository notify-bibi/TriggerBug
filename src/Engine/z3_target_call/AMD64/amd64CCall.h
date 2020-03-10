extern "C" {
#include "guest_amd64_defs.h"
}
#include "engine/variable.h"
#include "z3_target_defs.h"

Vns z3_amd64g_calculate_rflags_cf(ULong cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_amd64g_calculate_rflags_pf(ULong cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_amd64g_calculate_rflags_af(ULong cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_amd64g_calculate_rflags_zf(ULong cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_amd64g_calculate_rflags_sf(ULong cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_amd64g_calculate_rflags_of(ULong cc_op, Vns& cc_dep1_formal, Vns& cc_dep2_formal, Vns& cc_ndep_formal);
Vns z3_amd64g_calculate_condition(Vns/*AMD64Condcode*/& cond, Vns& cc_op, Vns& cc_dep1, Vns& cc_dep2, Vns& cc_ndep);
Vns z3_amd64g_calculate_rflags_c(Vns& cc_op, Vns& cc_dep1, Vns& cc_dep2, Vns& cc_ndep);
Vns z3_amd64g_calculate_rflags_all(Vns& cc_op, Vns& cc_dep1, Vns& cc_dep2, Vns& cc_ndep);