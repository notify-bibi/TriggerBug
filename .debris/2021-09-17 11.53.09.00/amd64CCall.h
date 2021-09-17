#program once
#include "instopt/engine/basic_var.hpp"

rsbool z3_amd64g_calculate_rflags_cf(int cc_op, const rsval<uint64_t>& cc_dep1_formal, const rsval<uint64_t>& cc_dep2_formal, const rsval<uint64_t>& cc_ndep_formal);
rsbool z3_amd64g_calculate_rflags_pf(int cc_op, const rsval<uint64_t>& cc_dep1_formal, const rsval<uint64_t>& cc_dep2_formal, const rsval<uint64_t>& cc_ndep_formal);
rsbool z3_amd64g_calculate_rflags_af(int cc_op, const rsval<uint64_t>& cc_dep1_formal, const rsval<uint64_t>& cc_dep2_formal, const rsval<uint64_t>& cc_ndep_formal);
rsbool z3_amd64g_calculate_rflags_zf(int cc_op, const rsval<uint64_t>& cc_dep1_formal, const rsval<uint64_t>& cc_dep2_formal, const rsval<uint64_t>& cc_ndep_formal);
rsbool z3_amd64g_calculate_rflags_sf(int cc_op, const rsval<uint64_t>& cc_dep1_formal, const rsval<uint64_t>& cc_dep2_formal, const rsval<uint64_t>& cc_ndep_formal);
rsbool z3_amd64g_calculate_rflags_of(int cc_op, const rsval<uint64_t>& cc_dep1_formal, const rsval<uint64_t>& cc_dep2_formal, const rsval<uint64_t>& cc_ndep_formal);

 rsval<uint64_t> z3_amd64g_calculate_condition(const rsval<uint64_t>/*AMD64Condcode*/& cond, const rsval<uint64_t>& cc_op, const rsval<uint64_t>& cc_dep1, const rsval<uint64_t>& cc_dep2, const rsval<uint64_t>& cc_ndep);
 rsval<uint64_t> z3_amd64g_calculate_rflags_c(const rsval<uint64_t>& cc_op, const rsval<uint64_t>& cc_dep1, const rsval<uint64_t>& cc_dep2, const rsval<uint64_t>& cc_ndep);
 rsval<uint64_t> z3_amd64g_calculate_rflags_all(const rsval<uint64_t>& cc_op, const rsval<uint64_t>& cc_dep1, const rsval<uint64_t>& cc_dep2, const rsval<uint64_t>& cc_ndep);