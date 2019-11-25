
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




#define caseIop_Arithmetic(OPNAME, OP, issigned) 												\
case Iop_##OPNAME##8:{																			\
	dassert(a.bitn == 8); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Char)(((issigned##Char)a)  OP  ((issigned##Char)b)));		    \
}																								\
case Iop_##OPNAME##16:{																			\
	dassert(a.bitn == 16); 																		\
	dassert(b.bitn == 16);																		\
	return Vns(m_ctx, (issigned##Short)(((issigned##Short)a)  OP  ((issigned##Short)b)));	    \
}																								\
case Iop_##OPNAME##32:{																			\
	dassert(a.bitn == 32); 																		\
	dassert(b.bitn == 32);																		\
	return Vns(m_ctx, (issigned##Int)(((issigned##Int)a)  OP  ((issigned##Int)b)));			    \
}																								\
case Iop_##OPNAME##64:{																			\
	dassert(a.bitn == 64); 																		\
	dassert(b.bitn == 64);																		\
	return Vns(m_ctx, (issigned##Long)(((issigned##Long)a)  OP  ((issigned##Long)b)));		    \
}

#define caseIop_Relational_Low(OPNAME, OP, issigned) 											\
case Iop_##OPNAME##8:{																			\
	dassert(a.bitn == 8); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Char)(((issigned##Char)a)  OP  ((issigned##Char)b)), 1);		\
}																								\
case Iop_##OPNAME##16:{																			\
	dassert(a.bitn == 16); 																		\
	dassert(b.bitn == 16);																		\
	return Vns(m_ctx, (issigned##Short)(((issigned##Short)a)  OP  ((issigned##Short)b)), 1);	\
}																								\

#define caseIop_Relational_High(OPNAME, OP, issigned, append) 									\
case Iop_##OPNAME##32##append:{																	\
	dassert(a.bitn == 32); 																		\
	dassert(b.bitn == 32);																		\
	return Vns(m_ctx, (issigned##Int)(((issigned##Int)a)  OP  ((issigned##Int)b)), 1);			\
}																								\
case Iop_##OPNAME##64##append:{																	\
	dassert(a.bitn == 64); 																		\
	dassert(b.bitn == 64);																		\
	return Vns(m_ctx, (issigned##Long)(((issigned##Long)a)  OP  ((issigned##Long)b)), 1);		\
}																								

#define caseIop_Bitwise(OPNAME, OP, issigned) 													\
case Iop_##OPNAME##8:{																			\
	dassert(a.bitn == 8); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Char)(((issigned##Char)a)  OP  ((issigned##Char)b)));			\
}																								\
case Iop_##OPNAME##16:{																			\
	dassert(a.bitn == 16); 																		\
	dassert(b.bitn == 16);																		\
	return Vns(m_ctx, (issigned##Short)(((issigned##Short)a)  OP  ((issigned##Short)b)));		\
}																								\
case Iop_##OPNAME##32:{																			\
	dassert(a.bitn == 32); 																		\
	dassert(b.bitn == 32);																		\
	return Vns(m_ctx, (issigned##Int)(((issigned##Int)a)  OP  ((issigned##Int)b)));				\
}																								\
case Iop_##OPNAME##64:{																			\
	dassert(a.bitn == 64); 																		\
	dassert(b.bitn == 64);																		\
	return Vns(m_ctx, (issigned##Long)(((issigned##Long)a)  OP  ((issigned##Long)b)));			\
}																								


#define caseIop_Bitwise_Shift(OPNAME, OP, issigned) 											\
case Iop_##OPNAME##8:{																			\
	dassert(a.bitn == 8); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Char)(((issigned##Char)a)  OP  ((issigned##Char)b)));		    \
}																								\
case Iop_##OPNAME##16:{																			\
	dassert(a.bitn == 16); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Short)(((issigned##Short)a)  OP  ((issigned##Char)b)));		\
}																								\
case Iop_##OPNAME##32:{																			\
	dassert(a.bitn == 32); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Int)(((issigned##Int)a)  OP  ((issigned##Char)b)));			\
}																								\
case Iop_##OPNAME##64:{																			\
	dassert(a.bitn == 64); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, (issigned##Long)(((issigned##Long)a)  OP  ((issigned##Char)b)));		    \
}																								\


#define Z3caseIop_Arithmetic(OPNAME, OP, issigned) 												\
case Iop_##OPNAME##8:{																			\
	dassert(a.bitn == 8); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 8);														\
}																								\
case Iop_##OPNAME##16:{																			\
	dassert(a.bitn == 16); 																		\
	dassert(b.bitn == 16);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 16);														\
}																								\
case Iop_##OPNAME##32:{																			\
	dassert(a.bitn == 32); 																		\
	dassert(b.bitn == 32);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 32);														\
}																								\
case Iop_##OPNAME##64:{																			\
	dassert(a.bitn == 64); 																		\
	dassert(b.bitn == 64);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 64);														\
}

#define Z3caseIop_Relational_Low(OPNAME, OP, issigned) 											\
case Iop_##OPNAME##8:{																			\
	dassert(a.bitn == 8); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx,bool2bv(m_ctx, OP(m_ctx, a, b)), 1);										\
}																								\
case Iop_##OPNAME##16:{																			\
	dassert(a.bitn == 16); 																		\
	dassert(b.bitn == 16);																		\
	return Vns(m_ctx,bool2bv(m_ctx, OP(m_ctx, a, b)), 1);										\
}																								\

#define Z3caseIop_Relational_High(OPNAME, OP, issigned, append) 								\
case Iop_##OPNAME##32##append:{																	\
	dassert(a.bitn == 32); 																		\
	dassert(b.bitn == 32);																		\
	return Vns(m_ctx,bool2bv(m_ctx, OP(m_ctx, a, b)), 1);										\
}																								\
case Iop_##OPNAME##64##append:{																	\
	dassert(a.bitn == 64); 																		\
	dassert(b.bitn == 64);																		\
	return Vns(m_ctx,bool2bv(m_ctx, OP(m_ctx, a, b)), 1);										\
}																								

#define Z3caseIop_Bitwise(OPNAME, OP, issigned) 												\
case Iop_##OPNAME##8:{																			\
	dassert(a.bitn == 8); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 8);														\
}																								\
case Iop_##OPNAME##16:{																			\
	dassert(a.bitn == 16); 																		\
	dassert(b.bitn == 16);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 16);														\
}																								\
case Iop_##OPNAME##32:{																			\
	dassert(a.bitn == 32); 																		\
	dassert(b.bitn == 32);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 32);														\
}																								\
case Iop_##OPNAME##64:{																			\
	dassert(a.bitn == 64); 																		\
	dassert(b.bitn == 64);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 64);														\
}																								


#define Z3caseIop_Bitwise_Shift(OPNAME, OP, issigned) 											\
case Iop_##OPNAME##8:{																			\
	dassert(a.bitn == 8); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, b), 8);														\
}																								\
case Iop_##OPNAME##16:{																			\
	dassert(a.bitn == 16); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, Vns(m_ctx, Z3_mk_zero_ext(m_ctx, 8, b), 16)), 16);			\
}																								\
case Iop_##OPNAME##32:{																			\
	dassert(a.bitn == 32); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, Vns(m_ctx, Z3_mk_zero_ext(m_ctx, 24, b), 32)), 32);			\
}																								\
case Iop_##OPNAME##64:{																			\
	dassert(a.bitn == 64); 																		\
	dassert(b.bitn == 8);																		\
	return Vns(m_ctx, OP(m_ctx, a, Vns(m_ctx, Z3_mk_zero_ext(m_ctx, 56, b), 64)), 64);			\
}																								\



inline Vns State::T_Binop(context &m_ctx, IROp op, Vns const& a, Vns const& b) {
    if (a.symbolic() || b.symbolic()) {
        goto dosymbol;
    }

    {
	    switch (op) {
	    caseIop_Arithmetic(Add, +, U);
	    caseIop_Arithmetic(Sub, -, U);
	    caseIop_Arithmetic(Mul, *, U);
					
	    case Iop_DivU32:{															
		    dassert(a.bitn == 32);
		    dassert(b.bitn == 32);
		    return Vns(m_ctx, (UInt)(((UInt)a)  /  ((UInt)b)));
	    }
	    case Iop_DivU64:{
		    dassert(a.bitn == 64);
		    dassert(b.bitn == 64);
		    return Vns(m_ctx, (ULong)(((ULong)a)  /  ((ULong)b)));
	    }
	    case Iop_DivS32: {
		    dassert(a.bitn == 32);
		    dassert(b.bitn == 32);
		    return Vns(m_ctx, (Int)(((Int)a) / ((Int)b)));
	    }
	    case Iop_DivS64: {
		    dassert(a.bitn == 64);
		    dassert(b.bitn == 64);
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
	    caseIop_Relational_High(ExpCmpNE,	!=, U,);
	    caseIop_Relational_High(CmpNE	,	!=, U,);
	    caseIop_Relational_High(CmpEQ	,	==, U,);
	    caseIop_Relational_High(CasCmpEQ,	==, U,);
	    caseIop_Relational_High(CasCmpNE,	!=, U,);

	    caseIop_Relational_High(CmpLE, <= , U, U);
	    caseIop_Relational_High(CmpLE, <= , S, S);
	    caseIop_Relational_High(CmpLT, < , U, U);
	    caseIop_Relational_High(CmpLT, < , S, S);


	    case Iop_XorV128:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_xor_si128(a, b));
	    case Iop_XorV256:dassert(a.bitn == 256); dassert(b.bitn == 256); return Vns(m_ctx, _mm256_xor_si256(a, b));
	    case Iop_OrV128:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_or_si128(a,b));//ok por     xmm2, xmm3
	    case Iop_OrV256:dassert(a.bitn == 256); dassert(b.bitn == 256); return Vns(m_ctx, _mm256_or_si256(a, b));//ok
	    case Iop_AndV128:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_and_pd(a, b));///ok andpd
	    case Iop_AndV256:dassert(a.bitn == 256); dassert(b.bitn == 256); return Vns(m_ctx, _mm256_and_pd(a, b));//ok

	    case Iop_Add8x16:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_add_epi8(a, b));
	    case Iop_Add16x8:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_add_epi16(a, b));
	    case Iop_Add32x4:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_add_epi32(a, b));
	    case Iop_Add64x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_add_epi64(a, b));
	    case Iop_Sub8x16:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_epi8(a, b));//ok psubb xmm1, xmm0
	    case Iop_Sub16x8:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_epi16(a, b));//ok psubb xmm1, xmm0
	    case Iop_Sub32x4:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_epi32(a, b));//ok
	    case Iop_Sub64x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_epi64(a, b));//ok

	    case Iop_Min8Ux16:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_min_epu8(a, b));//ok pminub  xmm0, xmm1
	    case Iop_Min16Ux8:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_min_epu16(a, b));//ok
	    case Iop_Min32Ux4:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_min_epu32(a, b));//ok
	    case Iop_Min64Ux2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_min_epu64(a, b));//ok


	    case Iop_CmpEQ64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_cmpneq_sd(a, b));
	    case Iop_CmpLT64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_cmpnlt_sd(a, b));
        case Iop_CmpLE64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); {//ok cmpnlesd xmm5, xmm1
            __m128i m128i = _mm_set1_epi16(0xff);
            return Vns(m_ctx, _mm_xor_pd(_mm_cmpnle_sd(a, b), *(__m128d*)(&m128i)));
        }
	    case Iop_CmpUN64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_cmpunord_pd(a, b));
		
	    case Iop_Add64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_add_sd(a, b));//ok addsd   xmm2, xmm0
	    case Iop_Sub64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_sub_sd(a, b));//ok subsd   xmm2, xmm0
	    case Iop_Mul64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_mul_sd(a, b));
	    case Iop_Div64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_div_sd(a, b));
	    case Iop_Max64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_max_sd(a, b));
	    case Iop_Min64F0x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_min_sd(a, b));

		

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

        case Iop_PermOrZero8x16: {dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_shuffle_epi8(a, b)); }

	    case Iop_ShlN8x16:dassert(a.bitn == 128); dassert(b.bitn == 8); goto FAILD;
	    case Iop_ShlN16x8:dassert(a.bitn == 128); dassert(b.bitn == 8); return Vns(m_ctx, _mm_slli_epi16(a, (UChar)b));
	    case Iop_ShlN32x4:dassert(a.bitn == 128); dassert(b.bitn == 8); return Vns(m_ctx, _mm_slli_epi32(a, (UChar)b));
	    case Iop_ShlN64x2:dassert(a.bitn == 128); dassert(b.bitn == 8); return Vns(m_ctx, _mm_slli_epi64(a, (UChar)b));
	    case Iop_InterleaveHI8x16:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_unpackhi_epi8(b, a));//true
	    case Iop_InterleaveHI16x8:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_unpackhi_epi16(b, a));//true
	    case Iop_InterleaveHI32x4:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_unpackhi_epi32(b, a));//ir error ,fixed args
	    case Iop_InterleaveHI64x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_unpackhi_epi64(b, a));//ir error ,fixed args

	    case Iop_InterleaveLO8x16:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_unpacklo_epi8(b, a));//true
	    case Iop_InterleaveLO16x8:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_unpacklo_epi16(b, a));//true
	    case Iop_InterleaveLO32x4:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_unpacklo_epi32(b, a));//ir error ,fixed args
	    case Iop_InterleaveLO64x2:dassert(a.bitn == 128); dassert(b.bitn == 128); return Vns(m_ctx, _mm_unpacklo_epi64(b, a));//ir error ,fixed args

	    case Iop_8HLto16:dassert(a.bitn == 8); dassert(b.bitn == 8); return Vns(m_ctx, (UShort)(((UShort)a << 8) | (UChar)b));
	    case Iop_16HLto32:dassert(a.bitn == 16); dassert(b.bitn == 16); return Vns(m_ctx, (UInt)((((UInt)(UShort)a) << 16) | (UShort)b));
	    case Iop_32HLto64:dassert(a.bitn == 32); dassert(b.bitn == 32); return Vns(m_ctx, (ULong)((((ULong)(UInt)a) << 32) | (UInt)b));
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

        case Iop_F64toF32: {return ((Int)a == 0) ? Vns(m_ctx, (float)((double)b)) : b.fp2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>(), m_ctx.fpa_sort<32>(), 32).simplify(); }

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
            dassert(a.bitn == 64); dassert(b.bitn == 32);
            ULong na = a; UInt nb = b;
            UInt rem, s;
            __asm__(
                "xor %%rcx,%%rcx;\n\t"
                "mov %[hi32],%%rdx;\n\t"
                "mov %[lo32],%%rax;\n\t"
                "mov %[bcs],%%ecx;\n\t"
                "idiv %%ecx;\n\t"
                "mov %%eax,%[s];\n\t"
                "mov %%edx,%[rem];\n\t"
                : [s] "=r"(s)[rem] "=r"(rem)
                : [hi32] "r"(na >> 32), [lo32] "r"(na & 0xffffffff), [bcs] "r"(nb)
                : "rax", "rdx", "rcx"
            );
            ULong re = (((ULong)rem) << 32) | s;
            return Vns(m_ctx, re);
	    }
	    case Iop_DivModU64to32: {
            dassert(a.bitn == 64); dassert(b.bitn == 32);
            ULong na = a; UInt nb = b;
            UInt rem, s;
            __asm__(
                "xor %%rcx,%%rcx;\n\t"
                "mov %[hi32],%%rdx;\n\t"
                "mov %[lo32],%%rax;\n\t"
                "mov %[bcs],%%ecx;\n\t"
                "div %%ecx;\n\t"
                "mov %%eax,%[s];\n\t"
                "mov %%edx,%[rem];\n\t"
                : [s] "=r"(s)[rem] "=r"(rem)
                : [hi32] "r"(na >> 32), [lo32] "r"(na & 0xffffffff), [bcs] "r"(nb)
                : "rax", "rdx", "rcx"
            );
            ULong re = (((ULong)rem) << 32) | s;
            return Vns(m_ctx, re);
	    }
	    case Iop_DivModU128to64: {//ok
		    dassert(a.bitn == 128); dassert(b.bitn == 64);
            __m128i na = a; ULong nb = b;
            __m128i re;
            __asm__(
                "mov %[hi64],%%rdx;\n\t"
                "mov %[lo64],%%rax;\n\t"
                "mov %[bcs],%%rcx;\n\t"
                "div %%rcx;\n\t"
                "mov %%rax,%[s];\n\t"
                "mov %%rdx,%[rem];\n\t"
                : [s] "=r"(re.m128i_u64[0])[rem] "=r"(re.m128i_u64[1])
                : [hi64] "r"(na.m128i_u64[1]), [lo64] "r"(na.m128i_u64[0]), [bcs] "r"(nb)
                : "rax", "rdx", "rcx"
            );
            return Vns(m_ctx, re);
	    }
	    case Iop_DivModS128to64: {
            dassert(a.bitn == 128); dassert(b.bitn == 64);
            __m128i na = a; ULong nb = b;
            __m128i re;
            __asm__(
                "mov %[hi64],%%rdx;\n\t"
                "mov %[lo64],%%rax;\n\t"
                "mov %[bcs],%%rcx;\n\t"
                "idiv %%rcx;\n\t"
                "mov %%rax,%[s];\n\t"
                "mov %%rdx,%[rem];\n\t"
                : [s] "=r"(re.m128i_u64[0])[rem] "=r"(re.m128i_u64[1])
                : [hi64] "r"(na.m128i_u64[1]), [lo64] "r"(na.m128i_u64[0]), [bcs] "r"(nb)
                : "rax", "rdx", "rcx"
            );
            return Vns(m_ctx, re);
	    }
        case Iop_MullU32: {
            dassert(a.bitn == 32); dassert(b.bitn == 32);
            UInt na = a; UInt nb = b;
            ULong re;
            __asm__(
                "xor %%rax,%%rax;\n\t"
                "xor %%rbx,%%rbx;\n\t"
                "mov %[a],%%eax;\n\t"
                "mov %[b],%%ebx;\n\t"
                "mul %%ebx;\n\t"
                "mov %%eax,%[lo32];\n\t"
                "mov %%edx,%[hi32];\n\t"
                : [lo32] "=r"(GET4(&re))[hi32] "=r"(((UInt*)&re)[1])
                : [a] "r"(na), [b] "r"(nb)
                : "rax", "edx"
            );
            return Vns(m_ctx, re);
        }
        case Iop_MullS32: {
            dassert(a.bitn == 32); dassert(b.bitn == 32);
            UInt na = a; UInt nb = b;
            ULong re;
            __asm__(
                "xor %%rax,%%rax;\n\t"
                "xor %%rbx,%%rbx;\n\t"
                "mov %[a],%%eax;\n\t"
                "mov %[b],%%ebx;\n\t"
                "imul %%ebx;\n\t"
                "mov %%eax,%[lo32];\n\t"
                "mov %%edx,%[hi32];\n\t"
                : [lo32] "=r"(GET4(&re))[hi32] "=r"(((UInt*)&re)[1])
                : [a] "r"(na), [b] "r"(nb)
                : "rax", "edx"
            );
            return Vns(m_ctx, re);
        }
	    case Iop_MullU64: {
            dassert(a.bitn == 64); dassert(b.bitn == 64);
            ULong na = a; ULong nb = b;
            __m128i re;
            __asm__(
                "mov %[a],%%rax;\n\t"
                "mov %[b],%%rbx;\n\t"
                "mul %%rbx;\n\t"
                "mov %%rax,%[lo64];\n\t"
                "mov %%rdx,%[hi64];\n\t"
                : [lo64] "=r"(re.m128i_u64[0])[hi64] "=r"(re.m128i_u64[1])
                : [a] "r"(na), [b] "r"(nb)
                : "rax", "edx"
            );
            return Vns(m_ctx, re);
	    }
	    case Iop_MullS64: {
            dassert(a.bitn == 64); dassert(b.bitn == 64);
            ULong na = a; ULong nb = b;
            __m128i re;
            __asm__(
                "mov %[a],%%rax;\n\t"
                "mov %[b],%%rbx;\n\t"
                "imul %%rbx;\n\t"
                "mov %%rax,%[lo64];\n\t"
                "mov %%rdx,%[hi64];\n\t"
                : [lo64] "=r"(re.m128i_u64[0])[hi64] "=r"(re.m128i_u64[1])
                : [a] "r"(na), [b] "r"(nb)
                : "rax", "edx"
            );
            return Vns(m_ctx, re);
	    }


	    default:ppIROp(op); vpanic("???wtf??");
	    }
	    goto FAILD;
    }
    {
dosymbol:
	switch (op) {
	Z3caseIop_Arithmetic(Add, Z3_mk_bvadd, U);
	Z3caseIop_Arithmetic(Sub, Z3_mk_bvsub, U);
	Z3caseIop_Arithmetic(Mul, Z3_mk_bvmul, U);

	case Iop_DivU32:{															
		dassert(a.bitn == 32);
		dassert(b.bitn == 32);
		return Vns(m_ctx, Z3_mk_bvudiv(m_ctx, a, b), 32);
	}
	case Iop_DivU64:{
		dassert(a.bitn == 64);
		dassert(b.bitn == 64);
		return Vns(m_ctx, Z3_mk_bvudiv(m_ctx, a, b), 64);
	}
	case Iop_DivS32: {
		dassert(a.bitn == 32);
		dassert(b.bitn == 32);
		return Vns(m_ctx, Z3_mk_bvsdiv(m_ctx, a, b), 32);
	}
	case Iop_DivS64: {
		dassert(a.bitn == 64);
		dassert(b.bitn == 64);
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

	Z3caseIop_Relational_High(ExpCmpNE, Z3_mk_neq, U, );
	Z3caseIop_Relational_High(CmpNE	,	Z3_mk_neq, U, );
	Z3caseIop_Relational_High(CmpEQ	,	Z3_mk_eq, U, );
	Z3caseIop_Relational_High(CasCmpEQ, Z3_mk_eq, U, );
	Z3caseIop_Relational_High(CasCmpNE, Z3_mk_neq, U, );

	Z3caseIop_Relational_High(CmpLE, Z3_mk_bvule, U, U);
	Z3caseIop_Relational_High(CmpLE, Z3_mk_bvule, S, S);
	Z3caseIop_Relational_High(CmpLT, Z3_mk_bvult, U, U);
	Z3caseIop_Relational_High(CmpLT, Z3_mk_bvult, S, S);

	case Iop_8HLto16:dassert(a.bitn == 8); dassert(b.bitn == 8); return Vns(m_ctx, Z3_mk_concat(m_ctx, a, b), 16);
	case Iop_16HLto32:dassert(a.bitn == 16); dassert(b.bitn == 16); return Vns(m_ctx, Z3_mk_concat(m_ctx, a, b), 32);
	case Iop_32HLto64:dassert(a.bitn == 32); dassert(b.bitn == 32); return Vns(m_ctx, Z3_mk_concat(m_ctx, a, b), 64);
	case Iop_64HLto128: 
	case Iop_64HLtoV128: dassert(a.bitn == 64); dassert(b.bitn == 64); return Vns(m_ctx, Z3_mk_concat(m_ctx, a, b), 128);

	case Iop_I64StoF64: { return b.integer2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()); }//ok
	case Iop_F64toI64S: { return b.fp2integer_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()); }//ok
	case Iop_I64UtoF64: { return b.uinteger2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()); }//ok
	case Iop_F64toI64U: { return b.fp2uinteger_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()); }//ok

	case Iop_I32StoF32: {return b.integer2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()); }//ok
	case Iop_F32toI32S: {return b.fp2integer_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()); }//ok
	case Iop_I32UtoF32: {return b.uinteger2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()); }//ok
	case Iop_F32toI32U: {return b.fp2uinteger_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()); }//ok

	case Iop_CmpF64: {
		Vns a = a.bv2fpa(m_ctx.fpa_sort<64>());
		Vns b = b.bv2fpa(m_ctx.fpa_sort<64>());
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
        dassert(a.bitn == 128); dassert(b.bitn == 64);
        Vns nb = b.zext(64);
        return Vns(m_ctx,
            Z3_mk_concat(m_ctx,
                Vns(m_ctx, Z3_mk_bvurem(m_ctx, a, nb), 128).extract(63, 0),
                Vns(m_ctx, Z3_mk_bvudiv(m_ctx, a, nb), 128).extract(63, 0)
            ), 128);
	}
	case Iop_DivModS128to64: {//ok
        dassert(a.bitn == 128); dassert(b.bitn == 64);
        Vns nb = b.sext(64);
        return Vns(m_ctx,
            Z3_mk_concat(m_ctx,
                Vns(m_ctx, Z3_mk_bvsrem(m_ctx, a, nb), 128).extract(63, 0),
                Vns(m_ctx, Z3_mk_bvsdiv(m_ctx, a, nb), 128).extract(63, 0)
            ), 128);
	}
	case Iop_DivModU64to32: {
        dassert(a.bitn == 64); dassert(b.bitn == 32);
        Vns nb = b.zext(32);
        return Vns(m_ctx,
            Z3_mk_concat(m_ctx,
                Vns(m_ctx, Z3_mk_bvurem(m_ctx, a, nb), 64).extract(31, 0),
                Vns(m_ctx, Z3_mk_bvudiv(m_ctx, a, nb), 64).extract(31, 0)
            ), 64);

	}
	case Iop_DivModS64to32: {
        dassert(a.bitn == 64); dassert(b.bitn == 32);
        Vns nb = b.sext(32);
        return Vns(m_ctx,
            Z3_mk_concat(m_ctx,
                Vns(m_ctx, Z3_mk_bvsrem(m_ctx, a, nb), 64).extract(31, 0),
                Vns(m_ctx, Z3_mk_bvsdiv(m_ctx, a, nb), 64).extract(31, 0)
            ), 64);

	}
    case Iop_MullU32: {
        dassert(a.bitn == 32);
        dassert(b.bitn == 32);
        return Vns(m_ctx, Z3_mk_bvmul(m_ctx, a.zext(32), b.zext(32)), 64);
    }
    case Iop_MullS32: {
        dassert(a.bitn == 32);
        dassert(b.bitn == 32);
        return Vns(m_ctx, Z3_mk_bvmul(m_ctx, a.sext(32), b.sext(32)), 64);
    }

#define BNxN(type,op, N, Mask)\
{\
    Vns re(m_ctx, 0, 0);\
    for (UInt i = 0; i < N; i++) {\
        re = ite(a.extract((i+1) * (sizeof(type)<<3)-1, i * (sizeof(type)<<3)) op b.extract((i+1) * (sizeof(type)<<3) -1, i * (sizeof(type)<<3)),\
                    Vns(m_ctx, (type)Mask), Vns(m_ctx, (type)0x0)).Concat(re);\
    }\
    return re;\
}
    case Iop_CmpEQ8x32: BNxN(UChar, ==, 32, 0xFF)
    case Iop_CmpEQ16x16: BNxN(UShort, == , 16, 0xFFFF)
    case Iop_CmpEQ32x8: BNxN(UInt, == , 8, 0xFFFFFFFF)
    case Iop_CmpEQ64x4: BNxN(ULong, == , 4, 0xFFFFFFFFFFFFFFFF)

    case Iop_CmpEQ8x16: BNxN(UChar, == , 16, 0xFF)
    case Iop_CmpEQ16x8: BNxN(UShort, == , 8, 0xFFFF)
    case Iop_CmpEQ32x4: BNxN(UInt, == , 4, 0xFFFFFFFF)
    case Iop_CmpEQ64x2: BNxN(ULong, == , 2, 0xFFFFFFFFFFFFFFFF)


	case Iop_ShrV128:goto FAILD;

	


	default:ppIROp(op); vpanic("???wtf??");
	}
    }
FAILD:
	ppIROp(op);
	vpanic("tIRType");

}

#undef BNxN
#undef caseIop_Arithmetic
#undef caseIop_Bitwise_Shift
#undef caseIop_Bitwise
#undef caseIop_Relational_Low
#undef caseIop_Relational_High
#undef Z3caseIop_Arithmetic
#undef Z3caseIop_Bitwise_Shift
#undef Z3caseIop_Bitwise
#undef Z3caseIop_Relational_High
#undef Z3caseIop_Relational_Low