#pragma once   
#ifndef TRANSLATE_IR_H
#define TRANSLATE_IR_H

#define CODEDEF1(name)					 \
switch (length) {						 \
case 8:vex_printf((name)); break;		 \
default:goto none;						 \
}break;								     \


#define CODEDEF2(length,name)			\
switch ((length)) {						\
case 1:vex_printf((name)); break;		\
default:goto none;						\
}break;									





//inline unsigned short mscv_tid2temp() {
//    UChar index;
//    __asm__(\
//        "movq %%gs:0x30, %%rax ;\n\t"\
//        "movl 0x48(%%rax),%%eax;\n\t"\
//        "movq %[list],%%rdx;\n\t"\
//        "movb (%%rdx,%%rax,1),%%al;\n\t"\
//        "movl %%al,%[out];\n\t"\
//        : [out] "=r"(index) : [list] "r"(tid2temp) : "rax", "rdx");
//
//    return index;
//}


inline int ty2length(IRType ty) {
	switch (ty) {
	case Ity_INVALID: vex_printf("Ity_INVALID"); break;
    case 1:
	case Ity_I1:      return 0;
    case 8:
	case Ity_I8:      return 1;
    case 16:
	case Ity_I16:     return 2;
    case Ity_F16:     return 2;
    case 32:
	case Ity_I32:     return 4;
    case Ity_D32:     return 4;
    case Ity_F32:     return 4;
    case 64:
	case Ity_I64:     return 8;
    case Ity_F64:     return 8;
    case Ity_D64:     return 8;
    case 128:
	case Ity_I128:    return 16;
	case Ity_F128:    return 16;
	case Ity_D128:    return 16;
	case Ity_V128:    return 16;
    case 256:
	case Ity_V256:    return 32;
	default:vpanic("ty2length");
	}
	return 0;
}

inline int ty2bit(IRType ty) {
    switch (ty) {
    case Ity_INVALID: vex_printf("Ity_INVALID"); break;
    case 1:
    case Ity_I1:      return 1;
    case 8:
    case Ity_I8:      return 8;
    case 16:
    case Ity_I16:     return 16;
    case Ity_F16:     return 16;
    case 32:
    case Ity_I32:     return 32;
    case Ity_F32:     return 32;
    case Ity_D32:     return 32;
    case 64:
    case Ity_I64:     return 64;
    case Ity_F64:     return 64;
    case Ity_D64:     return 64;
    case 128:
    case Ity_I128:    return 128;
    case Ity_F128:    return 128;
    case Ity_D128:    return 128;
    case Ity_V128:    return 128;
    case 256:
    case Ity_V256:    return 256;
    default:vpanic("ty2length");
    }
    return 0;
}

NORETURN
static z3::sort translateRM(z3::context&m_ctx, IRRoundingMode md) {
	switch (md)
	{
	case Irrm_NEAREST: return z3::sort(m_ctx, Z3_mk_fpa_rne(m_ctx));
	case Irrm_NegINF: return z3::sort(m_ctx, Z3_mk_fpa_rtn(m_ctx));
	case Irrm_PosINF: return z3::sort(m_ctx, Z3_mk_fpa_rtp(m_ctx));
	case Irrm_ZERO: return z3::sort(m_ctx, Z3_mk_fpa_rtz(m_ctx));
	case Irrm_NEAREST_TIE_AWAY_0: return z3::sort(m_ctx, Z3_mk_fpa_rna(m_ctx));
	default:
		vpanic("translateRM ???");
	}
}


static inline IRType length2ty(UShort bit) {
	switch (bit) {
	case 0:    return Ity_INVALID;
	case 1:    return Ity_I1;
	case 8:    return Ity_I8;
	case 16:   return Ity_I16;
	case 32:   return Ity_I32;
	case 64:   return Ity_I64;
	case 128:  return Ity_I128;
	case 256:  return Ity_V256;
	default:vpanic("length2ty");
	}
	return Ity_INVALID;
}

static inline int ico2length(IRConstTag tag) {
	int length = 0;
	switch (tag) {
	case Ity_INVALID: vex_printf("Ity_INVALID"); break;
	case Ico_U1:      length = 0;   break;
	case Ico_U8:      length = 1;   break;
	case Ico_U16:     length = 2;   break;
	case Ico_U32:     length = 4;   break;
	case Ico_U64:     length = 8;   break;
	case Ico_F32:     length = 4;   break;
	case Ico_F32i:     length = 4;   break;
	case Ico_F64:     length = 8;   break;
	case Ico_F64i:     length = 8;   break;
	case Ico_V128:    length = 16;   break;
	case Ico_V256:    length = 32;   break;
	default:vpanic("ico2length");
		length = 0;   break;
	}
	return length;
}
static inline void tAMD64REGS(int offset, int length) {
	vex_printf("\t\t");
	switch (offset) {
	case 16:
		switch (length) {
		case 8:vex_printf("rax"); break;
		case 4:vex_printf("eax"); break;
		case 2:vex_printf(" ax"); break;
		case 1:vex_printf(" al"); break;
		default:goto none;
		}break;
		CODEDEF2(17, "ah");
	case 24:
		switch (length) {
		case 8:vex_printf("rcx"); break;
		case 4:vex_printf("ecx"); break;
		case 2:vex_printf(" cx"); break;
		case 1:vex_printf(" cl"); break;
		default:goto none;
		}break;
		CODEDEF2(25, "ch");
	case 32: vex_printf("rdx"); break;
		switch (length) {
		case 8:vex_printf("rdx"); break;
		case 4:vex_printf("edx"); break;
		case 2:vex_printf(" dx"); break;
		case 1:vex_printf(" dl"); break;
		default:goto none;
		}break;
		CODEDEF2(33, "dh");
	case 40: vex_printf("rbx"); break;
		switch (length) {
		case 8:vex_printf("rbx"); break;
		case 4:vex_printf("ebx"); break;
		case 2:vex_printf(" bx"); break;
		case 1:vex_printf(" bl"); break;
		default:goto none;
		}break;
	case 48: vex_printf("rsp"); break;
		switch (length) {
		case 8:vex_printf("rsp"); break;
		case 4:vex_printf("esp"); break;
		default:goto none;
		}break;
	case 56: vex_printf("rbp"); break;
		switch (length) {
		case 8:vex_printf("rbp"); break;
		case 4:vex_printf("ebp"); break;
		default:goto none;
		}break;
	case 64: vex_printf("rsi"); break;
		switch (length) {
		case 8:vex_printf("rsi"); break;
		case 4:vex_printf("esi"); break;
		case 2:vex_printf(" si"); break;
		case 1:vex_printf("sil"); break;
		default:goto none;
		}break;
		CODEDEF2(65, "sih");
	case 72: vex_printf("rdi"); break;
		switch (length) {
		case 8:vex_printf("rdi"); break;
		case 4:vex_printf("edi"); break;
		case 2:vex_printf(" di"); break;
		case 1:vex_printf(" dil"); break;
		default:goto none;
		}break;
		CODEDEF2(73, "dih");
	case 80: vex_printf("r8"); break;
	case 88: vex_printf("r9"); break;
	case 96: vex_printf("r10"); break;
	case 104: vex_printf("r11"); break;
	case 112: vex_printf("r12"); break;
	case 120: vex_printf("r13"); break;
	case 128: vex_printf("r14"); break;
	case 136: vex_printf("r15"); break;
	case 144: vex_printf("cc_op"); break;
	case 152: vex_printf("cc_dep1"); break;
	case 160: vex_printf("cc_dep2"); break;
	case 168: vex_printf("cc_ndep"); break;
	case 176: vex_printf("d"); break;
	case 184: vex_printf("rip"); break;
	case 192: vex_printf("ac"); break;
	case 200: vex_printf("id"); break;
	case 208: vex_printf("fs"); break;
	case 216: vex_printf("sseround"); break;
	case 224:
		switch (length) {
		case 32:vex_printf("ymm0"); break;
		case 16:vex_printf("xmm0"); break;
		default:vex_printf("ymm0"); break;
		}break;
	case 256:
		switch (length) {
		case 32:vex_printf("ymm1"); break;
		case 16:vex_printf("xmm1"); break;
		default:vex_printf("ymm1"); break;
		}break;
	case 288:
		switch (length) {
		case 32:vex_printf("ymm2"); break;
		case 16:vex_printf("xmm2"); break;
		default:vex_printf("ymm2"); break;
		}break;
	case 320:
		switch (length) {
		case 32:vex_printf("ymm3"); break;
		case 16:vex_printf("xmm3"); break;
		default:vex_printf("ymm3"); break;
		}break;
	case 352:
		switch (length) {
		case 32:vex_printf("ymm4"); break;
		case 16:vex_printf("xmm4"); break;
		default:vex_printf("ymm4"); break;
		}break;
	case 384:
		switch (length) {
		case 32:vex_printf("ymm5"); break;
		case 16:vex_printf("xmm5"); break;
		default:vex_printf("ymm5"); break;
		}break;
	case 416:
		switch (length) {
		case 32:vex_printf("ymm6"); break;
		case 16:vex_printf("xmm6"); break;
		default:vex_printf("ymm6"); break;
		}break;
	case 448:
		switch (length) {
		case 32:vex_printf("ymm7"); break;
		case 16:vex_printf("xmm7"); break;
		default:vex_printf("ymm7"); break;
		}break;
	case 480:
		switch (length) {
		case 32:vex_printf("ymm8"); break;
		case 16:vex_printf("xmm8"); break;
		default:vex_printf("ymm8"); break;
		}break;
	case 512:
		switch (length) {
		case 32:vex_printf("ymm9"); break;
		case 16:vex_printf("xmm9"); break;
		default:vex_printf("ymm9"); break;
		}break;
	case 544:
		switch (length) {
		case 32:vex_printf("ymm10"); break;
		case 16:vex_printf("xmm10"); break;
		default:vex_printf("ymm10"); break;
		}break;
	case 576:
		switch (length) {
		case 32:vex_printf("ymm11"); break;
		case 16:vex_printf("xmm11"); break;
		default:vex_printf("ymm11"); break;
		}break;
	case 608:
		switch (length) {
		case 32:vex_printf("ymm12"); break;
		case 16:vex_printf("xmm12"); break;
		default:vex_printf("ymm12"); break;
		}break;
	case 640:
		switch (length) {
		case 32:vex_printf("ymm13"); break;
		case 16:vex_printf("xmm13"); break;
		default:vex_printf("ymm13"); break;
		}break;
	case 672:
		switch (length) {
		case 32:vex_printf("ymm14"); break;
		case 16:vex_printf("xmm14"); break;
		default:vex_printf("ymm14"); break;
		}break;
	case 704:
		switch (length) {
		case 32:vex_printf("ymm15"); break;
		case 16:vex_printf("xmm15"); break;
		default:vex_printf("ymm15"); break;
		}break;
	case 736:
		switch (length) {
		case 32:vex_printf("ymm16"); break;
		case 16:vex_printf("xmm16"); break;
		default:vex_printf("ymm16"); break;
		}break;
	case 768: vex_printf("ftop"); break;
	case 776:
		switch (length) {
		case 64:vex_printf("fpreg"); break;
		case 8:vex_printf("mm0"); break;
		default:vex_printf("fpreg"); break;
		}break;
	case 784: CODEDEF1("mm1")
	case 792: CODEDEF1("mm2")
	case 800: CODEDEF1("mm3")
	case 808: CODEDEF1("mm4")
	case 816: CODEDEF1("mm5")
	case 824: CODEDEF1("mm6")
	case 832: CODEDEF1("mm7")
	case 840: CODEDEF1("fptag")
	case 848: CODEDEF1("fpround")
	case 856: CODEDEF1("fc3210")
	case 864: {
		switch (length) {
		case 4:vex_printf("emnote"); break;
		default:goto none;
		}break;
	}
	case 872: CODEDEF1("cmstart")
	case 880: CODEDEF1("cmlen")
	case 888: CODEDEF1("nraddr")
	case 904: CODEDEF1("gs")
	case 912: CODEDEF1("ip_at_syscall")
	default:goto none;
	}
	return;
none:
	vex_printf(" what regoffset = %d ", offset);
}


#undef CODEDEF1
#undef CODEDEF2


#endif // !TRANSLATE_IR_H
