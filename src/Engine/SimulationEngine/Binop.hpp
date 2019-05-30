
#include <mmintrin.h>  //MMX
#include <xmmintrin.h> //SSE(include mmintrin.h)
#include <emmintrin.h> //SSE2(include xmmintrin.h)
#include <pmmintrin.h> //SSE3(include emmintrin.h)
#include <tmmintrin.h> //SSSE3(include pmmintrin.h)
#include <smmintrin.h> //SSE4.1(include tmmintrin.h)
#include <nmmintrin.h> //SSE4.2(include smmintrin.h)
#include <wmmintrin.h> //AES(include nmmintrin.h)
#include <immintrin.h> //AVX(include wmmintrin.h)
#include <intrin.h>    //(include immintrin.h)
#include <dvec.h>


typedef __m128i XMM;
#define xmbshl(x,n)  _mm_slli_si128(x,n) // xm <<= 8*n  -- BYTE shift left
#define xmbshr(x,n)  _mm_srli_si128(x,n) // xm >>= 8*n  -- BYTE shift right
#define xmshl64(x,n) _mm_slli_epi64(x,n) // xm.hi <<= n, xm.lo <<= n
#define xmshr64(x,n) _mm_srli_epi64(x,n) // xm.hi >>= n, xm.lo >>= n
#define xmand(a,b)   _mm_and_si128(a,b)
#define xmor(a,b)    _mm_or_si128(a,b)
#define xmxor(a,b)   _mm_xor_si128(a,b)
#define xmzero       _mm_setzero_si128()


#define caseIop_Arithmetic(OPNAME, OP, issigned) 												\
case Iop_##OPNAME##8:{																			\
	vassert(a.bitn == 8); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Char)(((issigned##Char)a)  OP  ((issigned##Char)b)));			\
}																								\
case Iop_##OPNAME##16:{																			\
	vassert(a.bitn == 16); 																		\
	vassert(b.bitn == 16);																		\
	return Vns(m_ctx, (issigned##Short)(((issigned##Short)a)  OP  ((issigned##Short)b)));		\
}																								\
case Iop_##OPNAME##32:{																			\
	vassert(a.bitn == 32); 																		\
	vassert(b.bitn == 32);																		\
	return Vns(m_ctx, (issigned##Int)(((issigned##Int)a)  OP  ((issigned##Int)b)));				\
}																								\
case Iop_##OPNAME##64:{																			\
	vassert(a.bitn == 64); 																		\
	vassert(b.bitn == 64);																		\
	return Vns(m_ctx, (issigned##Long)(((issigned##Long)a)  OP  ((issigned##Long)b)));			\
}

#define caseIop_Relational_Low(OPNAME, OP, issigned) 											\
case Iop_##OPNAME##8:{																			\
	vassert(a.bitn == 8); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Char)(((issigned##Char)a)  OP  ((issigned##Char)b)), 1);		\
}																								\
case Iop_##OPNAME##16:{																			\
	vassert(a.bitn == 16); 																		\
	vassert(b.bitn == 16);																		\
	return Vns(m_ctx, (issigned##Short)(((issigned##Short)a)  OP  ((issigned##Short)b)), 1);	\
}																								\

#define caseIop_Relational_High(OPNAME, OP, issigned, append) 									\
case Iop_##OPNAME##32##append:{																	\
	vassert(a.bitn == 32); 																		\
	vassert(b.bitn == 32);																		\
	return Vns(m_ctx, (issigned##Int)(((issigned##Int)a)  OP  ((issigned##Int)b)), 1);			\
}																								\
case Iop_##OPNAME##64##append:{																	\
	vassert(a.bitn == 64); 																		\
	vassert(b.bitn == 64);																		\
	return Vns(m_ctx, (issigned##Long)(((issigned##Long)a)  OP  ((issigned##Long)b)), 1);		\
}																								

#define caseIop_Bitwise(OPNAME, OP, issigned) 													\
case Iop_##OPNAME##8:{																			\
	vassert(a.bitn == 8); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Char)(((issigned##Char)a)  OP  ((issigned##Char)b)));			\
}																								\
case Iop_##OPNAME##16:{																			\
	vassert(a.bitn == 16); 																		\
	vassert(b.bitn == 16);																		\
	return Vns(m_ctx, (issigned##Short)(((issigned##Short)a)  OP  ((issigned##Short)b)));		\
}																								\
case Iop_##OPNAME##32:{																			\
	vassert(a.bitn == 32); 																		\
	vassert(b.bitn == 32);																		\
	return Vns(m_ctx, (issigned##Int)(((issigned##Int)a)  OP  ((issigned##Int)b)));				\
}																								\
case Iop_##OPNAME##64:{																			\
	vassert(a.bitn == 64); 																		\
	vassert(b.bitn == 64);																		\
	return Vns(m_ctx, (issigned##Long)(((issigned##Long)a)  OP  ((issigned##Long)b)));			\
}																								


#define caseIop_Bitwise_Shift(OPNAME, OP, issigned) 											\
case Iop_##OPNAME##8:{																			\
	vassert(a.bitn == 8); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Char)(((issigned##Char)a)  OP  ((issigned##Char)b)));			\
}																								\
case Iop_##OPNAME##16:{																			\
	vassert(a.bitn == 16); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Short)(((issigned##Short)a)  OP  ((issigned##Char)b)));		\
}																								\
case Iop_##OPNAME##32:{																			\
	vassert(a.bitn == 32); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Int)(((issigned##Int)a)  OP  ((issigned##Char)b)));			\
}																								\
case Iop_##OPNAME##64:{																			\
	vassert(a.bitn == 64); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Long)(((issigned##Long)a)  OP  ((issigned##Char)b)));			\
}																								\


#define Z3caseIop_Arithmetic(OPNAME, OP, issigned) 												\
case Iop_##OPNAME##8:{																			\
	vassert(a.bitn == 8); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 8);														\
}																								\
case Iop_##OPNAME##16:{																			\
	vassert(a.bitn == 16); 																		\
	vassert(b.bitn == 16);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 16);														\
}																								\
case Iop_##OPNAME##32:{																			\
	vassert(a.bitn == 32); 																		\
	vassert(b.bitn == 32);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 32);														\
}																								\
case Iop_##OPNAME##64:{																			\
	vassert(a.bitn == 64); 																		\
	vassert(b.bitn == 64);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 64);														\
}

#define Z3caseIop_Relational_Low(OPNAME, OP, issigned) 											\
case Iop_##OPNAME##8:{																			\
	vassert(a.bitn == 8); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx,bool2bv(m_ctx, OP(m_ctx, a, b)), 1);										\
}																								\
case Iop_##OPNAME##16:{																			\
	vassert(a.bitn == 16); 																		\
	vassert(b.bitn == 16);																		\
	return Vns(m_ctx,bool2bv(m_ctx, OP(m_ctx, a, b)), 1);										\
}																								\

#define Z3caseIop_Relational_High(OPNAME, OP, issigned, append) 								\
case Iop_##OPNAME##32##append:{																	\
	vassert(a.bitn == 32); 																		\
	vassert(b.bitn == 32);																		\
	return Vns(m_ctx,bool2bv(m_ctx, OP(m_ctx, a, b)), 1);										\
}																								\
case Iop_##OPNAME##64##append:{																	\
	vassert(a.bitn == 64); 																		\
	vassert(b.bitn == 64);																		\
	return Vns(m_ctx,bool2bv(m_ctx, OP(m_ctx, a, b)), 1);										\
}																								

#define Z3caseIop_Bitwise(OPNAME, OP, issigned) 												\
case Iop_##OPNAME##8:{																			\
	vassert(a.bitn == 8); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 8);														\
}																								\
case Iop_##OPNAME##16:{																			\
	vassert(a.bitn == 16); 																		\
	vassert(b.bitn == 16);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 16);														\
}																								\
case Iop_##OPNAME##32:{																			\
	vassert(a.bitn == 32); 																		\
	vassert(b.bitn == 32);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 32);														\
}																								\
case Iop_##OPNAME##64:{																			\
	vassert(a.bitn == 64); 																		\
	vassert(b.bitn == 64);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 64);														\
}																								


#define Z3caseIop_Bitwise_Shift(OPNAME, OP, issigned) 											\
case Iop_##OPNAME##8:{																			\
	vassert(a.bitn == 8); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 8);														\
}																								\
case Iop_##OPNAME##16:{																			\
	vassert(a.bitn == 16); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, Vns(m_ctx, Z3_mk_zero_ext(m_ctx, 8, b), 16)), 16);			\
}																								\
case Iop_##OPNAME##32:{																			\
	vassert(a.bitn == 32); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, Vns(m_ctx, Z3_mk_zero_ext(m_ctx, 24, b), 32)), 32);			\
}																								\
case Iop_##OPNAME##64:{																			\
	vassert(a.bitn == 64); 																		\
	vassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, Vns(m_ctx, Z3_mk_zero_ext(m_ctx, 56, b), 64)), 64);			\
}																								\



inline Vns State::T_Binop(IROp op, IRExpr* arg1, IRExpr* arg2) {
	Vns a = tIRExpr(arg1);
	Vns b = tIRExpr(arg2);
	if (a.symbolic() || b.symbolic()) goto dosymbol;
	switch (op) {
		caseIop_Arithmetic(Add, +, U);
		caseIop_Arithmetic(Sub, -, U);
		caseIop_Arithmetic(Mul, *, U);
	case Iop_DivU32:{															
		vassert(a.bitn == 32);
		vassert(b.bitn == 32);
		return Vns(m_ctx, (UInt)(((UInt)a)  /  ((UInt)b)));
	}
	case Iop_DivU64:{
		vassert(a.bitn == 64);
		vassert(b.bitn == 64);
		return Vns(m_ctx, (ULong)(((ULong)a)  /  ((ULong)b)));
	}
	case Iop_DivS32: {
		vassert(a.bitn == 32);
		vassert(b.bitn == 32);
		return Vns(m_ctx, (Int)(((Int)a) / ((Int)b)));
	}
	case Iop_DivS64: {
		vassert(a.bitn == 64);
		vassert(b.bitn == 64);
		return Vns(m_ctx, (Long)(((Long)a) / ((Long)b)));
	}

		caseIop_Bitwise(And, &, U);
		caseIop_Bitwise(Or , |, U);
		caseIop_Bitwise(Xor, ^, U);
		caseIop_Bitwise_Shift(Shl, <<, U);
		caseIop_Bitwise_Shift(Shr, >>, U);
		caseIop_Bitwise_Shift(Sar, >>, S);
		caseIop_Relational_Low(ExpCmpNE,	!=, U);
		caseIop_Relational_Low(CmpNE,		!=, U);
		caseIop_Relational_Low(CmpEQ,		==, U);
		caseIop_Relational_Low(CasCmpEQ,	==, U);
		caseIop_Relational_Low(CasCmpNE,	!=, U);
		caseIop_Relational_High(ExpCmpNE,	!=, U);
		caseIop_Relational_High(CmpNE	,	!=, U);
		caseIop_Relational_High(CmpEQ	,	==, U);
		caseIop_Relational_High(CasCmpEQ,	==, U);
		caseIop_Relational_High(CasCmpNE,	!=, U);

		caseIop_Relational_High(CmpLE, <= , U, U);
		caseIop_Relational_High(CmpLE, <= , S, S);
		caseIop_Relational_High(CmpLT, < , U, U);
		caseIop_Relational_High(CmpLT, < , S, S);


	case Iop_XorV128:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_xor_si128(a, b));
	case Iop_XorV256:vassert(a.bitn == 256); vassert(b.bitn == 256); return Vns(m_ctx, _mm256_xor_si256(a, b));
	case Iop_OrV128:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_or_si128(a,b));//ok por     xmm2, xmm3
	case Iop_OrV256:vassert(a.bitn == 256); vassert(b.bitn == 256); return Vns(m_ctx, _mm256_or_si256(a, b));//ok
	case Iop_AndV128:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_and_pd(a, b));///ok andpd
	case Iop_AndV256:vassert(a.bitn == 256); vassert(b.bitn == 256); return Vns(m_ctx, _mm256_and_pd(a, b));//ok

	case Iop_Add8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_add_epi8(a, b));
	case Iop_Add16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_add_epi16(a, b));
	case Iop_Add32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_add_epi32(a, b));
	case Iop_Add64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_add_epi64(a, b));
	case Iop_Sub8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_epi8(a, b));//ok psubb xmm1, xmm0
	case Iop_Sub16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_epi16(a, b));//ok psubb xmm1, xmm0
	case Iop_Sub32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_epi32(a, b));//ok
	case Iop_Sub64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_epi64(a, b));//ok

	case Iop_Min8Ux16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_min_epu8(a, b));//ok pminub  xmm0, xmm1
	case Iop_Min16Ux8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_min_epu16(a, b));//ok
	case Iop_Min32Ux4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_min_epu32(a, b));//ok
	case Iop_Min64Ux2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_min_epu64(a, b));//ok


	case Iop_CmpEQ64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_cmpneq_sd(a, b));
	case Iop_CmpLT64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_cmpnlt_sd(a, b));
	case Iop_CmpLE64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128);//ok cmpnlesd xmm5, xmm1
		__m128i m128i = _mm_set1_epi16(0xff);
		return Vns(m_ctx, _mm_xor_pd(_mm_cmpnle_sd(a, b), *(__m128d*)(&m128i)));
	case Iop_CmpUN64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_cmpunord_pd(a, b));
		
	case Iop_Add64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_add_sd(a, b));//ok addsd   xmm2, xmm0
	case Iop_Sub64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_sd(a, b));//ok subsd   xmm2, xmm0
	case Iop_Mul64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_mul_sd(a, b));
	case Iop_Div64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_div_sd(a, b));
	case Iop_Max64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_max_sd(a, b));
	case Iop_Min64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_min_sd(a, b));

		

	case Iop_CmpGT8Ux16: goto FAILD;
	case Iop_CmpGT16Ux8: goto FAILD;
	case Iop_CmpGT32Ux4: goto FAILD;
	case Iop_CmpGT64Ux2: goto FAILD;
	case Iop_CmpGT8Sx16:return Vns(m_ctx, _mm_cmpgt_epi8(a, b));//true
	case Iop_CmpGT16Sx8:return Vns(m_ctx, _mm_cmpgt_epi16(a, b));//true
	case Iop_CmpGT32Sx4:return Vns(m_ctx, _mm_cmpgt_epi32(a, b));//true
	case Iop_CmpGT64Sx2:return Vns(m_ctx, _mm_cmpgt_epi64(a, b));//true
	case Iop_CmpEQ8x16:return Vns(m_ctx, _mm_cmpeq_epi8(a, b));//ok  pcmpeqb
	case Iop_CmpEQ16x8:return Vns(m_ctx, _mm_cmpeq_epi16(a, b));//ok
	case Iop_CmpEQ32x4:return Vns(m_ctx, _mm_cmpeq_epi32(a, b));//ok
	case Iop_CmpEQ64x2:return Vns(m_ctx, _mm_cmpeq_epi64(a, b));//ok

	case Iop_CmpEQ8x32:return Vns(m_ctx, _mm256_cmpeq_epi8(a, b));//ok
	case Iop_CmpEQ16x16:return Vns(m_ctx, _mm256_cmpeq_epi16(a, b));//ok
	case Iop_CmpEQ32x8:return Vns(m_ctx, _mm256_cmpeq_epi32(a, b));//ok
	case Iop_CmpEQ64x4:return Vns(m_ctx, _mm256_cmpeq_epi64(a, b));//ok

	case Iop_ShlN8x16:vassert(a.bitn == 128); vassert(b.bitn == 8); goto FAILD;
	case Iop_ShlN16x8:vassert(a.bitn == 128); vassert(b.bitn == 8); return Vns(m_ctx, _mm_slli_epi16(a, (UChar)b));
	case Iop_ShlN32x4:vassert(a.bitn == 128); vassert(b.bitn == 8); return Vns(m_ctx, _mm_slli_epi32(a, (UChar)b));
	case Iop_ShlN64x2:vassert(a.bitn == 128); vassert(b.bitn == 8); return Vns(m_ctx, _mm_slli_epi64(a, (UChar)b));
	case Iop_InterleaveHI8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_unpackhi_epi8(b, a));//true
	case Iop_InterleaveHI16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_unpackhi_epi16(b, a));//true
	case Iop_InterleaveHI32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_unpackhi_epi32(b, a));//ir error ,fixed args
	case Iop_InterleaveHI64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_unpackhi_epi64(b, a));//ir error ,fixed args

	case Iop_InterleaveLO8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_unpacklo_epi8(b, a));//true
	case Iop_InterleaveLO16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_unpacklo_epi16(b, a));//true
	case Iop_InterleaveLO32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_unpacklo_epi32(b, a));//ir error ,fixed args
	case Iop_InterleaveLO64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Vns(m_ctx, _mm_unpacklo_epi64(b, a));//ir error ,fixed args

	case Iop_8HLto16:vassert(a.bitn == 8); vassert(b.bitn == 8); return Vns(m_ctx, (UShort)(((UShort)a << 8) | (UChar)b));
	case Iop_16HLto32:vassert(a.bitn == 16); vassert(b.bitn == 16); return Vns(m_ctx, (UInt)((((UInt)(UShort)a) << 16) | (UShort)b));
	case Iop_32HLto64:vassert(a.bitn == 32); vassert(b.bitn == 32); return Vns(m_ctx, (ULong)((((ULong)(UInt)a) << 32) | (UInt)b));
	case Iop_64HLto128: return Vns(m_ctx, _mm_set_epi64x(a, b));//ok
	case Iop_64HLtoV128: return Vns(m_ctx, _mm_set_epi64x(a, b));//ok

	
	case Iop_I64StoF64: {return ((Int)a == 0) ? Vns(m_ctx, (Double)((Long)b)) : b.integer2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()).simplify(); };//cvtsi2sd ok
	case Iop_F64toI64S: {return ((Int)a == 0) ? Vns(m_ctx, (Long)((Double)b)) : b.fp2integer_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()).simplify(); }//cvttsd2si rax, xmm1 ok
	case Iop_I64UtoF64: {return ((Int)a == 0) ? Vns(m_ctx, (Double)((ULong)b)) : b.uinteger2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()).simplify(); }// ok
	case Iop_F64toI64U: {return ((Int)a == 0) ? Vns(m_ctx, (ULong)((Double)b)) : b.fp2uinteger_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()).simplify(); }// ok

	case Iop_I32StoF32: {return ((Int)a == 0) ? Vns(m_ctx, (float)((Int)b)) : b.integer2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()).simplify(); }//ok
	case Iop_F32toI32S: {return ((Int)a == 0) ? Vns(m_ctx, (Int)((float)b)) : b.fp2integer_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()).simplify(); }//ok
	case Iop_I32UtoF32: {return ((Int)a == 0) ? Vns(m_ctx, (float)((UInt)b)) : b.uinteger2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()).simplify(); }//ok
	case Iop_F32toI32U: {return ((Int)a == 0) ? Vns(m_ctx, (UInt)((float)b)) : b.fp2uinteger_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()).simplify(); }//ok


	case Iop_CmpF64: {
		double da = a;
		double db = b;
		if (da == db) {
			return Vns(m_ctx, 0x40u);
		}
		else if (da < db) {
			return Vns(m_ctx, 0x01u);
		}
		else if (da > db){
			return Vns(m_ctx, 0x0u);
		}
		else {
			return Vns(m_ctx, 0x45u);
		}
	}
	case Iop_DivModS64to32: {
		vassert(a.bitn == 64);
		vassert(b.bitn == 32);
		UInt chushu = b;
		ULong beichushu = a;
		ULong result;
		__asm {
			movsx rdx, dword ptr(beichushu + 4)
			movsx rax, dword ptr(beichushu)
			idiv  chushu
			mov dword ptr(result + 4), edx
			mov dword ptr(result), eax
		}
		return Vns(m_ctx, result);
	}
	case Iop_DivModU64to32: {
		vassert(a.bitn == 64);
		vassert(b.bitn == 32);
		UInt chushu = b;
		ULong beichushu = a;
		ULong result;
		__asm {
			movzx rdx, dword ptr(beichushu + 4)
			movzx rax, dword ptr(beichushu)
			div  chushu
			mov dword ptr(result + 4), edx
			mov dword ptr(result), eax
		}
		return Vns(m_ctx, result);
	}
	case Iop_MullU32: {
		UInt chushu = b;
		ULong beichushu = a;
		ULong result;
		__asm {
			movzx eax, dword ptr(beichushu)
			mul  chushu
			mov qword ptr(result), rax
		}
		return Vns(m_ctx, result);
	}
	case Iop_MullS32: {
		UInt chushu = b;
		ULong beichushu = a;
		ULong result;
		__asm {
			movzx eax, dword ptr(beichushu)
			imul  chushu
			mov qword ptr(result), rax
		}
		return Vns(m_ctx, result);
	}


	case Iop_DivModU128to64: {//ok
		vassert(a.bitn == 128);
		vassert(b.bitn == 64);
		ULong chushu = b;
		__m128i beichushu = a;
		__m128i result;
		__asm {
			mov rdx, qword ptr(beichushu + 8)
			mov rax, qword ptr(beichushu)
			div chushu
			mov qword ptr(result + 8), rdx
			mov qword ptr(result), rax
		}
		return Vns(m_ctx, result);
	}
	case Iop_DivModS128to64: {
		vassert(a.bitn == 128);
		vassert(b.bitn == 64);
		ULong chushu = b;
		__m128i beichushu = a;
		__m128i result;
		__asm {
			mov rdx, qword ptr(beichushu + 8)
			mov rax, qword ptr(beichushu)
			idiv  chushu
			mov qword ptr(result + 8), rdx
			mov qword ptr(result), rax
		}
		return Vns(m_ctx, result);
	}

	

	case Iop_MullU64: {
		ULong along = a;
		ULong blong = b;
		__m128i result;
		__asm {
			mov rax, along
			mul blong
			mov qword ptr(result + 8), rdx
			mov  qword ptr(result), rax
		}
		return Vns(m_ctx, result);
	}

	case Iop_MullS64: {
		ULong along = a;
		ULong blong = b;
		__m128i result;

		__asm {
			mov rax, along
			imul blong
			mov qword ptr(result + 8), rdx
			mov  qword ptr(result), rax
		}
		return Vns(m_ctx, result);
	}

	case Iop_ShrV128:goto FAILD;

	default:ppIROp(op); vpanic("???wtf??");
	}
	goto FAILD;
dosymbol:
	switch (op) {
		Z3caseIop_Arithmetic(Add, Z3_mk_bvadd, U);
		Z3caseIop_Arithmetic(Sub, Z3_mk_bvsub, U);
		Z3caseIop_Arithmetic(Mul, Z3_mk_bvmul, U);
	case Iop_DivU32:{															
		vassert(a.bitn == 32);
		vassert(b.bitn == 32);
		return Vns(m_ctx, Z3_mk_bvudiv(m_ctx, a, b), 32);
	}
	case Iop_DivU64:{
		vassert(a.bitn == 64);
		vassert(b.bitn == 64);
		return Vns(m_ctx, Z3_mk_bvudiv(m_ctx, a, b), 64);
	}
	case Iop_DivS32: {
		vassert(a.bitn == 32);
		vassert(b.bitn == 32);
		return Vns(m_ctx, Z3_mk_bvsdiv(m_ctx, a, b), 32);
	}
	case Iop_DivS64: {
		vassert(a.bitn == 64);
		vassert(b.bitn == 64);
		return Vns(m_ctx, Z3_mk_bvsdiv(m_ctx, a, b), 64);
	}
		Z3caseIop_Bitwise(And, Z3_mk_bvand, U);
		Z3caseIop_Bitwise(Or , Z3_mk_bvor, U);
		Z3caseIop_Bitwise(Xor, Z3_mk_bvxor, U);
		Z3caseIop_Bitwise_Shift(Shl, Z3_mk_bvshl , U);
		Z3caseIop_Bitwise_Shift(Shr, Z3_mk_bvlshr, U);
		Z3caseIop_Bitwise_Shift(Sar, Z3_mk_bvashr, S);

		Z3caseIop_Relational_Low(ExpCmpNE,	Z3_mk_neq, U);
		Z3caseIop_Relational_Low(CmpNE,		Z3_mk_neq, U);
		Z3caseIop_Relational_Low(CmpEQ,		Z3_mk_eq, U);
		Z3caseIop_Relational_Low(CasCmpEQ,	Z3_mk_eq, U);
		Z3caseIop_Relational_Low(CasCmpNE,	Z3_mk_neq, U);

		Z3caseIop_Relational_High(ExpCmpNE, Z3_mk_neq, U);
		Z3caseIop_Relational_High(CmpNE	,	Z3_mk_neq, U);
		Z3caseIop_Relational_High(CmpEQ	,	Z3_mk_eq, U);
		Z3caseIop_Relational_High(CasCmpEQ, Z3_mk_eq, U);
		Z3caseIop_Relational_High(CasCmpNE, Z3_mk_neq, U);

		Z3caseIop_Relational_High(CmpLE, Z3_mk_bvule, U, U);
		Z3caseIop_Relational_High(CmpLE, Z3_mk_bvule, S, S);
		Z3caseIop_Relational_High(CmpLT, Z3_mk_bvult, U, U);
		Z3caseIop_Relational_High(CmpLT, Z3_mk_bvult, S, S);

	case Iop_8HLto16:vassert(a.bitn == 8); vassert(b.bitn == 8); return Vns(m_ctx, Z3_mk_concat(m_ctx, a, b), 16);
	case Iop_16HLto32:vassert(a.bitn == 16); vassert(b.bitn == 16); return Vns(m_ctx, Z3_mk_concat(m_ctx, a, b), 32);
	case Iop_32HLto64:vassert(a.bitn == 32); vassert(b.bitn == 32); return Vns(m_ctx, Z3_mk_concat(m_ctx, a, b), 64);
	case Iop_64HLto128: 
	case Iop_64HLtoV128: vassert(a.bitn == 64); vassert(b.bitn == 64); return Vns(m_ctx, Z3_mk_concat(m_ctx, a, b), 128);

	case Iop_I64StoF64: { return b.integer2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()); }//ok
	case Iop_F64toI64S: { return b.fp2integer_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()); }//ok
	case Iop_I64UtoF64: { return b.uinteger2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()); }//ok
	case Iop_F64toI64U: { return b.fp2uinteger_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()); }//ok

	case Iop_I32StoF32: {return b.integer2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()); }//ok
	case Iop_F32toI32S: {return b.fp2integer_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()); }//ok
	case Iop_I32UtoF32: {return b.uinteger2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()); }//ok
	case Iop_F32toI32U: {return b.fp2uinteger_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()); }//ok

	case Iop_CmpF64: {
		a = a.bv2fpa(m_ctx.fpa_sort<64>());
		b = b.bv2fpa(m_ctx.fpa_sort<64>());
		return Vns(m_ctx,
			ite(expr(m_ctx, Z3_mk_fpa_eq(m_ctx, a, b)),
				m_ctx.bv_val(0x40, 32),
				ite(expr(m_ctx, Z3_mk_fpa_lt(m_ctx, a, b)),
					m_ctx.bv_val(0x01, 32),
					ite(expr(m_ctx, Z3_mk_fpa_gt(m_ctx, a, b)),
						m_ctx.bv_val(0x00, 32),
						m_ctx.bv_val(0x45, 32)
					)
				)
			), 32);
	}
	case Iop_DivModU128to64: {//ok
		vassert(a.bitn == 128);
		vassert(b.bitn == 64);
		Vns beichushu = b.zext(64);
		return Vns(m_ctx,
			Z3_mk_concat(m_ctx,
			(a % beichushu).extract(63, 0),
				(a / beichushu).extract(63, 0)
			), 128);
	}
	case Iop_DivModS128to64: {//ok
		vassert(a.bitn == 128);
		vassert(b.bitn == 64);
		Vns beichushu = b.zext(64);
		
		return Vns(m_ctx,
			Z3_mk_concat(m_ctx,
			(a % beichushu).extract(63, 0) - ite(lt(a, 0), b, Vns(0ull, 64)),
				expr(m_ctx, Z3_mk_bvsdiv(m_ctx, a, beichushu)).extract(63, 0)
			), 128);
	}
	case Iop_DivModU64to32: {
		vassert(a.bitn == 64);
		vassert(b.bitn == 32);
		Vns beichushu = b.zext(32);
		return Vns(m_ctx,
			Z3_mk_concat(m_ctx,
			(a % beichushu).extract(31, 0),
				(a / beichushu).extract(31, 0)
			), 64);
	}

	case Iop_DivModS64to32: {
		vassert(a.bitn == 64);
		vassert(b.bitn == 32);
		Vns beichushu = b.zext(32);
		return Vns(m_ctx,
			Z3_mk_concat(m_ctx,
			(a % beichushu).extract(31, 0) - ite(lt(a, 0), b, Vns(0ull, 32)),
				Vns(m_ctx, Z3_mk_bvsdiv(m_ctx, a, beichushu), 64).extract(31, 0)
			), 64);
	}


	case Iop_ShrV128:goto FAILD;

	


	default:ppIROp(op); vpanic("???wtf??");
	}

FAILD:
	ppIROp(op);
	vpanic("tIRType");

}
