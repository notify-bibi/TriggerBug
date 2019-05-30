extern "C" {
#include "guest_amd64_defs.h"
}

#include "CCall_defs.hpp"






#define z3_amd64g_calculate_rflags_(FLAG)													\
inline static Vns z3_amd64g_calculate_rflags_##FLAG(										\
	ULong cc_op,																			\
	Vns &cc_dep1_formal,																	\
	Vns &cc_dep2_formal,																	\
	Vns &cc_ndep_formal) 																	\
{																							\
	switch (cc_op) {																		\
	case AMD64G_CC_OP_COPY:																	\
		return cc_dep1_formal																\
			& (AMD64G_CC_MASK_O | AMD64G_CC_MASK_S | AMD64G_CC_MASK_Z						\
				| AMD64G_CC_MASK_A | AMD64G_CC_MASK_C | AMD64G_CC_MASK_P);					\
																							\
	case AMD64G_CC_OP_ADDB:   ACTIONS_ADD_##FLAG(8, UChar_extract);							\
	case AMD64G_CC_OP_ADDW:   ACTIONS_ADD_##FLAG(16, UShort_extract);						\
	case AMD64G_CC_OP_ADDL:   ACTIONS_ADD_##FLAG(32, UInt_extract);							\
	case AMD64G_CC_OP_ADDQ:   ACTIONS_ADD_##FLAG(64, ULong_extract);						\
																							\
	case AMD64G_CC_OP_ADCB:   ACTIONS_ADC_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_ADCW:   ACTIONS_ADC_##FLAG(16, UShort_extract );						\
	case AMD64G_CC_OP_ADCL:   ACTIONS_ADC_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_ADCQ:   ACTIONS_ADC_##FLAG(64, ULong_extract );						\
																							\
	case AMD64G_CC_OP_SUBB:   ACTIONS_SUB_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_SUBW:   ACTIONS_SUB_##FLAG(16, UShort_extract );						\
	case AMD64G_CC_OP_SUBL:   ACTIONS_SUB_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_SUBQ:   ACTIONS_SUB_##FLAG(64, ULong_extract );						\
																							\
	case AMD64G_CC_OP_SBBB:   ACTIONS_SBB_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_SBBW:   ACTIONS_SBB_##FLAG(16, UShort_extract );						\
	case AMD64G_CC_OP_SBBL:   ACTIONS_SBB_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_SBBQ:   ACTIONS_SBB_##FLAG(64, ULong_extract );						\
																							\
	case AMD64G_CC_OP_LOGICB: ACTIONS_LOGIC_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_LOGICW: ACTIONS_LOGIC_##FLAG(16, UShort_extract );					\
	case AMD64G_CC_OP_LOGICL: ACTIONS_LOGIC_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_LOGICQ: ACTIONS_LOGIC_##FLAG(64, ULong_extract );						\
																							\
	case AMD64G_CC_OP_INCB:   ACTIONS_INC_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_INCW:   ACTIONS_INC_##FLAG(16, UShort_extract );						\
	case AMD64G_CC_OP_INCL:   ACTIONS_INC_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_INCQ:   ACTIONS_INC_##FLAG(64, ULong_extract );						\
										 													\
	case AMD64G_CC_OP_DECB:   ACTIONS_DEC_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_DECW:   ACTIONS_DEC_##FLAG(16, UShort_extract );						\
	case AMD64G_CC_OP_DECL:   ACTIONS_DEC_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_DECQ:   ACTIONS_DEC_##FLAG(64, ULong_extract );						\
										 													\
	case AMD64G_CC_OP_SHLB:   ACTIONS_SHL_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_SHLW:   ACTIONS_SHL_##FLAG(16, UShort_extract );						\
	case AMD64G_CC_OP_SHLL:   ACTIONS_SHL_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_SHLQ:   ACTIONS_SHL_##FLAG(64, ULong_extract );						\
										 													\
	case AMD64G_CC_OP_SHRB:   ACTIONS_SHR_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_SHRW:   ACTIONS_SHR_##FLAG(16, UShort_extract );						\
	case AMD64G_CC_OP_SHRL:   ACTIONS_SHR_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_SHRQ:   ACTIONS_SHR_##FLAG(64, ULong_extract );						\
										 													\
	case AMD64G_CC_OP_ROLB:   ACTIONS_ROL_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_ROLW:   ACTIONS_ROL_##FLAG(16, UShort_extract );						\
	case AMD64G_CC_OP_ROLL:   ACTIONS_ROL_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_ROLQ:   ACTIONS_ROL_##FLAG(64, ULong_extract );						\
										 													\
	case AMD64G_CC_OP_RORB:   ACTIONS_ROR_##FLAG(8, UChar_extract );						\
	case AMD64G_CC_OP_RORW:   ACTIONS_ROR_##FLAG(16, UShort_extract );						\
	case AMD64G_CC_OP_RORL:   ACTIONS_ROR_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_RORQ:   ACTIONS_ROR_##FLAG(64, ULong_extract );						\
																							\
																							\
	case AMD64G_CC_OP_ANDN32: ACTIONS_ANDN_##FLAG(32, UInt_extract);						\
	case AMD64G_CC_OP_ANDN64: ACTIONS_ANDN_##FLAG(64, ULong_extract );						\
																							\
	case AMD64G_CC_OP_BLSI32: ACTIONS_BLSI_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_BLSI64: ACTIONS_BLSI_##FLAG(64, ULong_extract );						\
																							\
	case AMD64G_CC_OP_BLSMSK32: ACTIONS_BLSMSK_##FLAG(32, UInt_extract );					\
	case AMD64G_CC_OP_BLSMSK64: ACTIONS_BLSMSK_##FLAG(64, ULong_extract );					\
																							\
	case AMD64G_CC_OP_BLSR32: ACTIONS_BLSR_##FLAG(32, UInt_extract );						\
	case AMD64G_CC_OP_BLSR64: ACTIONS_BLSR_##FLAG(64, ULong_extract );						\
																							\
	case AMD64G_CC_OP_ADCX32: ACTIONS_ADX_##FLAG(32, UInt_extract, C );						\
	case AMD64G_CC_OP_ADCX64: ACTIONS_ADX_##FLAG(64, ULong_extract, C );					\
																							\
	case AMD64G_CC_OP_ADOX32: ACTIONS_ADX_##FLAG(32, UInt_extract, O );						\
	case AMD64G_CC_OP_ADOX64: ACTIONS_ADX_##FLAG(64, ULong_extract, O );					\
																							\
																							\
																							\
																							\
																							\
																							\
																							\
																							\
	/*case AMD64G_CC_OP_UMULB:  ACTIONS_UMUL_##FLAG(8, UChar, toUChar,						\
		UShort, toUShort);																	\
	case AMD64G_CC_OP_UMULW:  ACTIONS_UMUL_##FLAG(16, UShort, toUShort,						\
		UInt, toUInt);																		\
	case AMD64G_CC_OP_UMULL:  ACTIONS_UMUL_##FLAG(32, UInt, toUInt,							\
		ULong, idULong);																	\
																							\
	case AMD64G_CC_OP_UMULQ:  ACTIONS_UMULQ_;												\
																							\
	case AMD64G_CC_OP_SMULB:  ACTIONS_SMUL_##FLAG(8, Char, toUChar,							\
		Short, toUShort);				  													\
	case AMD64G_CC_OP_SMULW:  ACTIONS_SMUL_##FLAG(16, Short, toUShort,						\
		Int, toUInt);					  													\
	case AMD64G_CC_OP_SMULL:  ACTIONS_SMUL_##FLAG(32, Int, toUInt,							\
		Long, idULong);																		\
																							\
	case AMD64G_CC_OP_SMULQ:  ACTIONS_SMULQ_;*/												\
																							\
	default:																				\
		/* shouldn't really make these calls from generated code */							\
		vex_printf("amd64g_calculate_rflags_all_WRK(AMD64)"									\
			"( %llu, 0x%llx, 0x%llx, 0x%llx )\n",											\
			cc_op, cc_dep1_formal, cc_dep2_formal, cc_ndep_formal);							\
		vpanic("amd64g_calculate_rflags_all_WRK(AMD64)");									\
	}																						\
}						






z3_amd64g_calculate_rflags_(cf);
z3_amd64g_calculate_rflags_(pf);
z3_amd64g_calculate_rflags_(af);
z3_amd64g_calculate_rflags_(zf);
z3_amd64g_calculate_rflags_(sf);
z3_amd64g_calculate_rflags_(of);



/* CALLED FROM GENERATED CODE: CLEAN HELPER */
/* returns 1 or 0 */

static inline Vns _z3_amd64g_calculate_condition(ULong/*AMD64Condcode*/ cond,
	ULong cc_op,
	Vns &cc_dep1,
	Vns &cc_dep2,
	Vns &cc_ndep)
{
	switch (cond) {
	case AMD64CondNO:
	case AMD64CondO: /* OF == 1 */
		return  z3_amd64g_calculate_rflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep);

	case AMD64CondNZ:
	case AMD64CondZ: /* ZF == 1 */
		return  z3_amd64g_calculate_rflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep);

	case AMD64CondNB:
	case AMD64CondB: /* CF == 1 */
		return  z3_amd64g_calculate_rflags_cf(cc_op, cc_dep1, cc_dep2, cc_ndep);


	case AMD64CondNBE:
	case AMD64CondBE: /* (CF or ZF) == 1 */
		return  z3_amd64g_calculate_rflags_cf(cc_op, cc_dep1, cc_dep2, cc_ndep) || z3_amd64g_calculate_rflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep);


	case AMD64CondNS:
	case AMD64CondS: /* SF == 1 */
		return  z3_amd64g_calculate_rflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep);

	case AMD64CondNP:
	case AMD64CondP: /* PF == 1 */
		return  z3_amd64g_calculate_rflags_pf(cc_op, cc_dep1, cc_dep2, cc_ndep);

	case AMD64CondNL:
	case AMD64CondL: /* (SF xor OF) == 1 */
		return z3_amd64g_calculate_rflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep).boolXor(z3_amd64g_calculate_rflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep));
				


	case AMD64CondNLE:
	case AMD64CondLE: /* ((SF xor OF) or ZF)  == 1 */ {
		auto sf = z3_amd64g_calculate_rflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep);
		auto of = z3_amd64g_calculate_rflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep);
		auto zf = z3_amd64g_calculate_rflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep);

		/*std::cout << sf.simplify()<<std::endl;
		std::cout << of.simplify() << std::endl;
		std::cout << zf.simplify() << std::endl;*/

		return   (sf.boolXor(of)) || zf;
	}
	default:
		/* shouldn't really make these calls from generated code */
		vex_printf("amd64g_calculate_condition"
			"( %llu, %llu, 0x%llx, 0x%llx, 0x%llx )\n",
			cond, cc_op, cc_dep1, cc_dep2, cc_ndep);
		vpanic("amd64g_calculate_condition");
	}
}


Vns z3_amd64g_calculate_condition(Vns/*AMD64Condcode*/ &cond,
	Vns &cc_op,
	Vns &cc_dep1,
	Vns &cc_dep2,
	Vns &cc_ndep)
{
	return Vns(cond,
		Z3_mk_ite(
			cond,
			((ULong)cond & 1) ? Z3_mk_not(cond, _z3_amd64g_calculate_condition(cond, cc_op, cc_dep1, cc_dep2, cc_ndep)):_z3_amd64g_calculate_condition(cond, cc_op, cc_dep1, cc_dep2, cc_ndep),
			Vns(cond, 1ull, 64),
			Vns(cond, 0ull, 64)
		), 64
	);
}


