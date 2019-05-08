#pragma once
#ifndef LIBVEX_INIT
#define LIBVEX_INIT

__attribute__((noreturn))
void failure_exit() {
	QueryPerformanceCounter(&closePerformanceCount_global);
	double delta_seconds = (double)(closePerformanceCount_global.QuadPart - beginPerformanceCount_global.QuadPart) / freq_global.QuadPart;
	printf("failure_exit  %s line:%d spend %f \n", __FILE__, __LINE__, delta_seconds);
	throw (z3::exception("failure_exit exception  "));
}
static void vex_log_bytes(const HChar* bytes, SizeT nbytes) {
	std::cout << bytes;
}

void vex_hwcaps_vai(VexArch arch, VexArchInfo *vai) {
	switch (arch) {
	case VexArchX86:
		vai->hwcaps = VEX_HWCAPS_X86_MMXEXT |
			VEX_HWCAPS_X86_SSE1 |
			VEX_HWCAPS_X86_SSE2 |
			VEX_HWCAPS_X86_SSE3 |
			VEX_HWCAPS_X86_LZCNT;
		break;
	case VexArchAMD64:
		vai->hwcaps = 
			VEX_HWCAPS_AMD64_SSE3 |
			VEX_HWCAPS_AMD64_SSSE3 |
			VEX_HWCAPS_AMD64_CX16 |
			VEX_HWCAPS_AMD64_LZCNT |
			VEX_HWCAPS_AMD64_AVX |
			VEX_HWCAPS_AMD64_RDTSCP |
			VEX_HWCAPS_AMD64_BMI |
			VEX_HWCAPS_AMD64_AVX2;
		break;
	case VexArchARM:
		vai->hwcaps = VEX_ARM_ARCHLEVEL(8) |
			VEX_HWCAPS_ARM_NEON |
			VEX_HWCAPS_ARM_VFP3;
		break;
	case VexArchARM64:
		vai->hwcaps = 0;
		vai->arm64_dMinLine_lg2_szB = 6;
		vai->arm64_iMinLine_lg2_szB = 6;
		break;
	case VexArchPPC32:
		vai->hwcaps = VEX_HWCAPS_PPC32_F |
			VEX_HWCAPS_PPC32_V |
			VEX_HWCAPS_PPC32_FX |
			VEX_HWCAPS_PPC32_GX |
			VEX_HWCAPS_PPC32_VX |
			VEX_HWCAPS_PPC32_DFP |
			VEX_HWCAPS_PPC32_ISA2_07;
		vai->ppc_icache_line_szB = 32; 
		break;
	case VexArchPPC64:
		vai->hwcaps = VEX_HWCAPS_PPC64_V |
			VEX_HWCAPS_PPC64_FX |
			VEX_HWCAPS_PPC64_GX |
			VEX_HWCAPS_PPC64_VX |
			VEX_HWCAPS_PPC64_DFP |
			VEX_HWCAPS_PPC64_ISA2_07;
		vai->ppc_icache_line_szB = 64;
		break;
	case VexArchS390X:
		vai->hwcaps = 0;
		break;
	case VexArchMIPS32:
	case VexArchMIPS64:
		vai->hwcaps = VEX_PRID_COMP_CAVIUM;
		break;
	default:
		std::cout << "Invalid arch in vex_prepare_vai.\n" << std::endl;
		break;
	}
}
void vex_prepare_vbi(VexArch arch, VexAbiInfo *vbi) {
	// only setting the guest_stack_redzone_size for now
	// this attribute is only specified by the X86, AMD64 and PPC64 ABIs

	switch (arch) {
	case VexArchX86:
		vbi->guest_stack_redzone_size = 0;
		break;
	case VexArchAMD64:
		vbi->guest_stack_redzone_size = 128;
		break;
	case VexArchPPC64:
		vbi->guest_stack_redzone_size = 288;
		break;
	default:
		break;
	}
}
static UInt needs_self_check(void *callback_opaque, VexRegisterUpdates* pxControl, const VexGuestExtents *guest_extents) {
	//std::cout << "needs_self_check\n" << std::endl;
	return 0;
}
static void *dispatch(void) {
	std::cout << "dispatch\n" << std::endl;
	return NULL;
}


#endif