
#include "instopt/engine/basic_var.hpp"
#include "z3_target_defs.h"

rsbool z3_x86g_calculate_eflags_cf(UInt cc_op, const rsval<uint32_t>& cc_dep1_formal, const rsval<uint32_t>& cc_dep2_formal, const rsval<uint32_t>& cc_ndep_formal);
rsbool z3_x86g_calculate_eflags_pf(UInt cc_op, const rsval<uint32_t>& cc_dep1_formal, const rsval<uint32_t>& cc_dep2_formal, const rsval<uint32_t>& cc_ndep_formal);
rsbool z3_x86g_calculate_eflags_af(UInt cc_op, const rsval<uint32_t>& cc_dep1_formal, const rsval<uint32_t>& cc_dep2_formal, const rsval<uint32_t>& cc_ndep_formal);
rsbool z3_x86g_calculate_eflags_zf(UInt cc_op, const rsval<uint32_t>& cc_dep1_formal, const rsval<uint32_t>& cc_dep2_formal, const rsval<uint32_t>& cc_ndep_formal);
rsbool z3_x86g_calculate_eflags_sf(UInt cc_op, const rsval<uint32_t>& cc_dep1_formal, const rsval<uint32_t>& cc_dep2_formal, const rsval<uint32_t>& cc_ndep_formal);
rsbool z3_x86g_calculate_eflags_of(UInt cc_op, const rsval<uint32_t>& cc_dep1_formal, const rsval<uint32_t>& cc_dep2_formal, const rsval<uint32_t>& cc_ndep_formal);

 rsval<uint32_t> z3_x86g_calculate_eflags_c(const rsval<uint32_t>& cc_op, const rsval<uint32_t>& cc_dep1, const rsval<uint32_t>& cc_dep2, const rsval<uint32_t>& cc_ndep);
 rsval<uint32_t> z3_x86g_calculate_condition(const rsval<uint32_t>&/*X86Condcode*/ cond, const rsval<uint32_t>& cc_op, const rsval<uint32_t>& cc_dep1, const rsval<uint32_t>& cc_dep2, const rsval<uint32_t>& cc_ndep);
 rsval<uint32_t> z3_x86g_calculate_eflags_all(const rsval<uint32_t>& cc_op, const rsval<uint32_t>& cc_dep1, const rsval<uint32_t>& cc_dep2, const rsval<uint32_t>& cc_ndep);