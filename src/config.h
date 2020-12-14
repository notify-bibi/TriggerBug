
#ifdef __cplusplus  
extern "C" {
#endif 

	extern void bb_insn_control_obj_set(void* instance, const UChar* (*guest_insn_control_method)(void*, Addr, Long, const UChar*));
	extern const UChar* /*out guest_code*/ guest_generic_bb_insn_control(Addr guest_IP_sbstart, Long delta,  /*in guest_code*/ const UChar* guest_code);

#ifndef GEN_MKG

#define MKG_VAR_CALL(NAME_SPACE, TYPE, VAR) extern TYPE* NAME_SPACE##_##VAR##_var_call();

#endif

	/* Declarations of this file */

	/*amd64*/
#ifdef MKG_AMD64
	MKG_VAR_CALL(amd64, VexEndness, host_endness)
		MKG_VAR_CALL(amd64, const UChar*, guest_code)
		MKG_VAR_CALL(amd64, Addr64, guest_RIP_bbstart)
		MKG_VAR_CALL(amd64, Addr64, guest_RIP_curr_instr)
		MKG_VAR_CALL(amd64, IRSB*, irsb)
		MKG_VAR_CALL(amd64, Addr64, guest_RIP_next_assumed)
		MKG_VAR_CALL(amd64, Bool, guest_RIP_next_mustcheck)

#endif

		/*x86*/
#ifdef MKG_X86
		MKG_VAR_CALL(x86, VexEndness, host_endness)
		MKG_VAR_CALL(x86, const UChar*, guest_code)
		MKG_VAR_CALL(x86, Addr64, guest_EIP_bbstart)
		MKG_VAR_CALL(x86, Addr64, guest_EIP_curr_instr)
		MKG_VAR_CALL(x86, IRSB*, irsb)
#endif

		/*arm*/
#ifdef MKG_ARM
		MKG_VAR_CALL(arm, VexEndness, host_endness)
		MKG_VAR_CALL(arm, Addr32, guest_R15_curr_instr_notENC)
		MKG_VAR_CALL(arm, Bool, __curr_is_Thumb)
		MKG_VAR_CALL(arm, IRSB*, irsb)
		MKG_VAR_CALL(arm, Bool, r15written)
		MKG_VAR_CALL(arm, IRTemp, r15guard)
		MKG_VAR_CALL(arm, IRTemp, r15kind)
#endif

		/*arm64*/
#ifdef MKG_ARM64
		MKG_VAR_CALL(arm64, VexEndness, host_endness)
		MKG_VAR_CALL(arm64, Addr64, guest_PC_curr_instr)
		MKG_VAR_CALL(arm64, IRSB*, irsb)
#endif

		/*mips*/
#ifdef MKG_MIPS
		MKG_VAR_CALL(mips, VexEndness, host_endness)
		MKG_VAR_CALL(mips, const UChar*, guest_code)
		MKG_VAR_CALL(mips, Addr64, guest_PC_curr_instr)
		MKG_VAR_CALL(mips, IRSB*, irsb)
		MKG_VAR_CALL(mips, Bool, mode64)
		MKG_VAR_CALL(mips, Bool, fp_mode64)
		MKG_VAR_CALL(mips, Bool, fp_mode64_fre)
		MKG_VAR_CALL(mips, Bool, has_msa)
#endif

		/*nanomips*/
#ifdef MKG_NANOMIPS
		MKG_VAR_CALL(nanomips, IRSB*, irsb)
		MKG_VAR_CALL(nanomips, Addr32, guest_PC_curr_instr)
#endif

		/*ppc*/
#ifdef MKG_PPC
		MKG_VAR_CALL(ppc, VexEndness, host_endness)
		MKG_VAR_CALL(ppc, const UChar*, guest_code)
		MKG_VAR_CALL(ppc, Addr64, guest_CIA_bbstart)
		MKG_VAR_CALL(ppc, Addr64, guest_CIA_curr_instr)
		MKG_VAR_CALL(ppc, IRSB*, irsb)
		MKG_VAR_CALL(ppc, Bool, mode64)
		MKG_VAR_CALL(ppc, Bool, OV32_CA32_supported)
#endif

		/*mipsdsp*/
		/*no global*/

		/*s390*/



#ifdef __cplusplus  
}
#endif 