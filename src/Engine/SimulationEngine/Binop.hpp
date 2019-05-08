
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

#define  SIMD(operator) 



inline Z3_ast Z3_mk_neq_incref(Z3_context ctx, Z3_ast a, Z3_ast b) { 
	auto eq = Z3_mk_eq(ctx, a, b);
	Z3_inc_ref(ctx,eq);
	auto re = Z3_mk_not(ctx, eq);
	Z3_inc_ref(ctx, re);
	Z3_dec_ref(ctx, eq);
	return re;
}

typedef __m128i XMM;
#define xmbshl(x,n)  _mm_slli_si128(x,n) // xm <<= 8*n  -- BYTE shift left
#define xmbshr(x,n)  _mm_srli_si128(x,n) // xm >>= 8*n  -- BYTE shift right
#define xmshl64(x,n) _mm_slli_epi64(x,n) // xm.hi <<= n, xm.lo <<= n
#define xmshr64(x,n) _mm_srli_epi64(x,n) // xm.hi >>= n, xm.lo >>= n
#define xmand(a,b)   _mm_and_si128(a,b)
#define xmor(a,b)    _mm_or_si128(a,b)
#define xmxor(a,b)   _mm_xor_si128(a,b)
#define xmzero       _mm_setzero_si128()


#define comma ,1

#define iop_template(OPNAME)			  \
template<UChar,UChar>					  \
inline Variable Iop_##OPNAME##(Variable &a,Variable &b){vassert(0);return Variable();}\
template<UChar,UChar>							  \
inline Variable Z3Iop_##OPNAME##(Variable &a, Variable &b) {vassert(0);return Variable();}

#define iop_template_bitwishe(OPNAME,OP,issigned,argtwo)			  \
template<>												  \
inline Variable Iop_##OPNAME##<8,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 8); vassert(b.bitn == 8);        return Variable((issigned##Char)( ((issigned##Char)a)  OP  ((issigned##Char)b) ), a argtwo);}	 \
template<>												  \
inline Variable Iop_##OPNAME##<16,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 16); vassert(b.bitn == 16);	 return Variable((issigned##Short)( ((issigned##Short)a)  OP  ((issigned##Short)b) ), a argtwo);}\
template<>												  \
inline Variable Iop_##OPNAME##<32,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 32); vassert(b.bitn == 32);	 return Variable((issigned##Int)( ((issigned##Int)a)  OP  ((issigned##Int)b) ), a argtwo);}		 \
template<>												  \
inline Variable Iop_##OPNAME##<64,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 64); vassert(b.bitn == 64);	 return Variable((issigned##Long)( ((issigned##Long)a)  OP  ((issigned##Long)b) ), a argtwo );}		    


#define Iop_template_shift(OPNAME,OP,issigned)			  \
template<>												  \
inline Variable Iop_##OPNAME##<8,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 8); vassert(b.bitn == 8);     return Variable((issigned##Char)( ((issigned##Char)a)  OP  ((UChar)b) ), a );}			\
template<>												  \
inline Variable Iop_##OPNAME##<16,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 16); vassert(b.bitn == 8);	  return Variable((issigned##Short)( ((issigned##Short)a)  OP  ((UChar)b) ), a );}		\
template<>												  \
inline Variable Iop_##OPNAME##<32,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 32); vassert(b.bitn == 8);	  return Variable((issigned##Int)( ((issigned##Int)a)  OP  ((UChar)b) ), a );}		    \
template<>												  \
inline Variable Iop_##OPNAME##<64,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 64); vassert(b.bitn == 8);	  return Variable((issigned##Long)( ((issigned##Long)a)  OP  ((UChar)b) ), a );}		    


#define iop_template_bitwishe_Z3(OPNAME,OP,issigned)	  \
template<>												  \
inline Variable Z3Iop_##OPNAME##<8,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 8); vassert(b.bitn == 8);        return Variable(a,OP(a,a,b) ,8);}				\
template<>												  \
inline Variable Z3Iop_##OPNAME##<16,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 16); vassert(b.bitn == 16);        return Variable(a,OP(a,a,b) ,16);}			\
template<>												  \
inline Variable Z3Iop_##OPNAME##<32,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 32); vassert(b.bitn == 32);        return Variable(a,OP(a,a,b) ,32);}			\
template<>												  \
inline Variable Z3Iop_##OPNAME##<64,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 64); vassert(b.bitn == 64);        return Variable(a,OP(a,a,b) ,64);}			\

#define iop_template_bitwishe_compare_Z3(OPNAME,OP,issigned)		  \
template<>												  \
inline Variable Z3Iop_##OPNAME##<8,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 8); vassert(b.bitn == 8);        return Variable(a,False,bool2bv(a,OP(a,a,b)) ,1);}				\
template<>												  \
inline Variable Z3Iop_##OPNAME##<16,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 16); vassert(b.bitn == 16);        return Variable(a,False,bool2bv(a,OP(a,a,b)) ,1);}			\
template<>												  \
inline Variable Z3Iop_##OPNAME##<32,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 32); vassert(b.bitn == 32);        return Variable(a,False,bool2bv(a,OP(a,a,b)) ,1);}			\
template<>												  \
inline Variable Z3Iop_##OPNAME##<64,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 64); vassert(b.bitn == 64);        return Variable(a,False,bool2bv(a,OP(a,a,b)) ,1);}			\


#define Iop_template_shift_Z3(OPNAME,OP,issigned)		  \
template<>												  \
inline Variable Z3Iop_##OPNAME##<8,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 8); vassert(b.bitn == 8);        return Variable(a,OP(a,a,b) ,8);}				\
template<>												  \
inline Variable Z3Iop_##OPNAME##<16,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 16); vassert(b.bitn == 8); auto tmp_ast=Z3_mk_zero_ext(b,8,b); Z3_inc_ref(b,tmp_ast);return Variable(a,OP(a,a,tmp_ast),tmp_ast,16);}\
template<>												  \
inline Variable Z3Iop_##OPNAME##<32,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 32); vassert(b.bitn == 8); auto tmp_ast=Z3_mk_zero_ext(b,24,b);Z3_inc_ref(b,tmp_ast);return Variable(a,OP(a,a,tmp_ast),tmp_ast,32);}\
template<>												  \
inline Variable Z3Iop_##OPNAME##<64,#@issigned>(Variable &a,Variable &b){vassert(a.bitn == 64); vassert(b.bitn == 8); auto tmp_ast=Z3_mk_zero_ext(b,56,b);Z3_inc_ref(b,tmp_ast);return Variable(a,OP(a,a,tmp_ast),tmp_ast,64);}


iop_template(Add)
iop_template_bitwishe(Add, +, U,)
iop_template_bitwishe_Z3(Add, Z3_mk_bvadd,U)
iop_template(Sub)
iop_template_bitwishe(Sub, -, U,)
iop_template_bitwishe_Z3(Sub, Z3_mk_bvsub, U)
iop_template(Mul)
iop_template_bitwishe(Mul, *, U,)
iop_template_bitwishe_Z3(Mul, Z3_mk_bvmul, U)
iop_template(Div)
iop_template_bitwishe(Div, /, U,)
iop_template_bitwishe(Div, /, S,)
iop_template_bitwishe_Z3(Div, Z3_mk_bvudiv, U)
iop_template_bitwishe_Z3(Div, Z3_mk_bvsdiv, S)

iop_template(And)
iop_template_bitwishe(And, &, U,)
iop_template_bitwishe_Z3(And, Z3_mk_bvand, U)
iop_template(Or)
iop_template_bitwishe(Or, | , U,)
iop_template_bitwishe_Z3(Or, Z3_mk_bvor, U)
iop_template(Xor)
iop_template_bitwishe(Xor, ^, U,)
iop_template_bitwishe_Z3(Xor, Z3_mk_bvxor, U)

iop_template(Shl)
Iop_template_shift(Shl, << , U)
Iop_template_shift_Z3(Shl, Z3_mk_bvshl, U)
iop_template(Shr)
Iop_template_shift(Shr, >> , U)
Iop_template_shift_Z3(Shr, Z3_mk_bvlshr, U)
iop_template(Sar)
Iop_template_shift(Sar, >> , S)
Iop_template_shift_Z3(Sar, Z3_mk_bvashr, S)


iop_template(ExpCmpNE)
iop_template_bitwishe(ExpCmpNE, !=, U, comma)
iop_template_bitwishe_compare_Z3(ExpCmpNE, Z3_mk_neq_incref, U)
iop_template(CmpNE)
iop_template_bitwishe(CmpNE, != , U, comma)
iop_template_bitwishe_compare_Z3(CmpNE, Z3_mk_neq_incref, U)
iop_template(CasCmpNE)
iop_template_bitwishe(CasCmpNE, != , U, comma)
iop_template_bitwishe_compare_Z3(CasCmpNE, Z3_mk_neq_incref, U)
iop_template(CmpEQ)
iop_template_bitwishe(CmpEQ, ==, U, comma)
iop_template_bitwishe_compare_Z3(CmpEQ, Z3_mk_eq,U)
iop_template(CasCmpEQ)
iop_template_bitwishe(CasCmpEQ, == , U, comma)
iop_template_bitwishe_compare_Z3(CasCmpEQ, Z3_mk_eq, U)
iop_template(CmpLE)
iop_template_bitwishe(CmpLE, <= , U, comma)
iop_template_bitwishe(CmpLE, <= , S, comma)
iop_template_bitwishe_compare_Z3(CmpLE, Z3_mk_bvule,U)
iop_template_bitwishe_compare_Z3(CmpLE, Z3_mk_bvsle,S)
iop_template(CmpLT)
iop_template_bitwishe(CmpLT, < , U, comma)
iop_template_bitwishe(CmpLT, < , S, comma)
iop_template_bitwishe_compare_Z3(CmpLT, Z3_mk_bvult, U)
iop_template_bitwishe_compare_Z3(CmpLT, Z3_mk_bvslt, S)

#define caseIop(OPNAME,issigned) 											\
case Iop_##OPNAME##8:return Iop_##OPNAME##<8,#@issigned>(a, b);				\
case Iop_##OPNAME##16:return Iop_##OPNAME##<16,#@issigned>(a, b);			\
case Iop_##OPNAME##32:return Iop_##OPNAME##<32,#@issigned>(a, b);			\
case Iop_##OPNAME##64:return Iop_##OPNAME##<64,#@issigned>(a, b);				  



#define Z3_caseIop(OPNAME,issigned) 											\
case Iop_##OPNAME##8:return Z3Iop_##OPNAME##<8,#@issigned>(a, b);				\
case Iop_##OPNAME##16:return Z3Iop_##OPNAME##<16,#@issigned>(a, b);			\
case Iop_##OPNAME##32:return Z3Iop_##OPNAME##<32,#@issigned>(a, b);			\
case Iop_##OPNAME##64:return Z3Iop_##OPNAME##<64,#@issigned>(a, b);				  



inline Variable State::T_Binop(IROp op, IRExpr* arg1, IRExpr* arg2) {
	Variable a = tIRExpr(arg1);
	Variable b = tIRExpr(arg2);

//#if defined(_DEBUG)&&defined(OPSTR)
//	{
//		a.tostr(); b.tostr();
//		vex_printf("\n");
//	}
//#endif
	if (a.symbolic() || b.symbolic()) goto dosymbol;
	switch (op) {
		caseIop(Add, U);
		caseIop(Sub, U);
		caseIop(Mul, U);
		caseIop(And, U);
		caseIop(Or, U);
		caseIop(Xor, U);
		caseIop(Shl, U);
		caseIop(Shr, U);
		caseIop(Sar, S);
		caseIop(ExpCmpNE, U);
		caseIop(CmpNE, U);
		caseIop(CmpEQ, U);
		caseIop(CasCmpEQ, U);
		caseIop(CasCmpNE, U);

	case Iop_CmpLE32U:return Iop_CmpLE<32, 'U'>(a, b);
	case Iop_CmpLE64U:return Iop_CmpLE<64, 'U'>(a, b);
	case Iop_CmpLE32S:return Iop_CmpLE<32, 'S'>(a, b);
	case Iop_CmpLE64S:return Iop_CmpLE<64, 'S'>(a, b);
	case Iop_CmpLT32U:return Iop_CmpLT<32, 'U'>(a, b);
	case Iop_CmpLT64U:return Iop_CmpLT<64, 'U'>(a, b);
	case Iop_CmpLT32S:return Iop_CmpLT<32, 'S'>(a, b);
	case Iop_CmpLT64S:return Iop_CmpLT<64, 'S'>(a, b);

	case Iop_DivU32:return Iop_Div<32, 'U'>(a, b);
	case Iop_DivS32:return Iop_Div<32, 'S'>(a, b);
	case Iop_DivU64:return Iop_Div<64, 'U'>(a, b);
	case Iop_DivS64:return Iop_Div<64, 'S'>(a, b);

	case Iop_XorV128:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_xor_si128(a, b),a );
	case Iop_XorV256:vassert(a.bitn == 256); vassert(b.bitn == 256); return Variable(_mm256_xor_si256(a, b), a);
	case Iop_OrV128:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_or_si128(a,b), a);//ok por     xmm2, xmm3
	case Iop_OrV256:vassert(a.bitn == 256); vassert(b.bitn == 256); return Variable(_mm256_or_si256(a, b), a);//ok
	case Iop_AndV128:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_and_pd(a, b), a);///ok andpd
	case Iop_AndV256:vassert(a.bitn == 256); vassert(b.bitn == 256); return Variable(_mm256_and_pd(a, b), a);//ok

	case Iop_Add8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_add_epi8(a, b), a);
	case Iop_Add16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_add_epi16(a, b), a);
	case Iop_Add32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_add_epi32(a, b), a);
	case Iop_Add64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_add_epi64(a, b), a);
	case Iop_Sub8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_sub_epi8(a, b), a);//ok psubb xmm1, xmm0
	case Iop_Sub16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_sub_epi16(a, b), a);//ok psubb xmm1, xmm0
	case Iop_Sub32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_sub_epi32(a, b), a);//ok
	case Iop_Sub64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_sub_epi64(a, b), a);//ok

	case Iop_Min8Ux16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_min_epu8(a, b), a);//ok pminub  xmm0, xmm1
	case Iop_Min16Ux8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_min_epu16(a, b), a);//ok
	case Iop_Min32Ux4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_min_epu32(a, b), a);//ok
	case Iop_Min64Ux2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_min_epu64(a, b), a);//ok


	case Iop_CmpEQ64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_cmpneq_sd(a, b), a);
	case Iop_CmpLT64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_cmpnlt_sd(a, b), a);
	case Iop_CmpLE64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128);//
		__m128i m128i = _mm_set1_epi16(0xff);
		return Variable(_mm_xor_pd(_mm_cmpnle_sd(a, b), *(__m128d*)(&m128i)), a);//ok cmpnlesd xmm5, xmm1
	case Iop_CmpUN64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_cmpunord_pd(a, b), a);
		
	case Iop_Add64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_add_sd(a, b), a);//ok addsd   xmm2, xmm0
	case Iop_Sub64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_sub_sd(a, b), a);//ok subsd   xmm2, xmm0
	case Iop_Mul64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_mul_sd(a, b), a);
	case Iop_Div64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_div_sd(a, b), a);
	case Iop_Max64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_max_sd(a, b), a);
	case Iop_Min64F0x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_min_sd(a, b), a);

		

	case Iop_CmpGT8Ux16: goto FAILD;
	case Iop_CmpGT16Ux8: goto FAILD;
	case Iop_CmpGT32Ux4: goto FAILD;
	case Iop_CmpGT64Ux2: goto FAILD;
	case Iop_CmpGT8Sx16:return Variable(_mm_cmpgt_epi8(a, b), a);//true
	case Iop_CmpGT16Sx8:return Variable(_mm_cmpgt_epi16(a, b), a);//true
	case Iop_CmpGT32Sx4:return Variable(_mm_cmpgt_epi32(a, b), a);//true
	case Iop_CmpGT64Sx2:return Variable(_mm_cmpgt_epi64(a, b), a);//true
	case Iop_CmpEQ8x16:return Variable(_mm_cmpeq_epi8(a, b), a);//ok  pcmpeqb
	case Iop_CmpEQ16x8:return Variable(_mm_cmpeq_epi16(a, b), a);//ok
	case Iop_CmpEQ32x4:return Variable(_mm_cmpeq_epi32(a, b), a);//ok
	case Iop_CmpEQ64x2:return Variable(_mm_cmpeq_epi64(a, b), a);//ok

	case Iop_CmpEQ8x32:return Variable(_mm256_cmpeq_epi8(a, b), a);//ok
	case Iop_CmpEQ16x16:return Variable(_mm256_cmpeq_epi16(a, b), a);//ok
	case Iop_CmpEQ32x8:return Variable(_mm256_cmpeq_epi32(a, b), a);//ok
	case Iop_CmpEQ64x4:return Variable(_mm256_cmpeq_epi64(a, b), a);//ok

	case Iop_ShlN8x16:vassert(a.bitn == 128); vassert(b.bitn == 8); goto FAILD;
	case Iop_ShlN16x8:vassert(a.bitn == 128); vassert(b.bitn == 8); return Variable(_mm_slli_epi16(a, (UChar)b), a);
	case Iop_ShlN32x4:vassert(a.bitn == 128); vassert(b.bitn == 8); return Variable(_mm_slli_epi32(a, (UChar)b), a);
	case Iop_ShlN64x2:vassert(a.bitn == 128); vassert(b.bitn == 8); return Variable(_mm_slli_epi64(a, (UChar)b), a);
	case Iop_InterleaveHI8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpackhi_epi8(b, a), a);//true
	case Iop_InterleaveHI16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpackhi_epi16(b, a), a);//true
	case Iop_InterleaveHI32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpackhi_epi32(b, a), a);//ir error ,fixed args
	case Iop_InterleaveHI64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpackhi_epi64(b, a), a);//ir error ,fixed args

	case Iop_InterleaveLO8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpacklo_epi8(b, a), a);//true
	case Iop_InterleaveLO16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpacklo_epi16(b, a), a);//true
	case Iop_InterleaveLO32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpacklo_epi32(b, a), a);//ir error ,fixed args
	case Iop_InterleaveLO64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpacklo_epi64(b, a), a);//ir error ,fixed args

	case Iop_8HLto16:vassert(a.bitn == 8); vassert(b.bitn == 8); return Variable((UShort)(((UShort)a << 8) | (UChar)b), a);
	case Iop_16HLto32:vassert(a.bitn == 16); vassert(b.bitn == 16); return Variable((UInt)((((UInt)(UShort)a) << 16) | (UShort)b), a);
	case Iop_32HLto64:vassert(a.bitn == 32); vassert(b.bitn == 32); return Variable((ULong)((((ULong)(UInt)a) << 32) | (UInt)b), a);
	case Iop_64HLto128: return Variable(_mm_set_epi64x(a, b), a);//ok
	case Iop_64HLtoV128: return Variable(_mm_set_epi64x(a, b), a);//ok

	
	case Iop_I64StoF64: {return ((Int)a == 0) ? Variable((Double)((Long)b), m_ctx) : b.integer2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()).simplify(); };//cvtsi2sd ok
	case Iop_F64toI64S: {return ((Int)a == 0) ? Variable((Long)((Double)b), m_ctx) : b.fp2integer_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()).simplify(); }//cvttsd2si rax, xmm1 ok
	case Iop_I64UtoF64: {return((Int)a == 0) ? Variable((Double)((ULong)b), m_ctx) : b.uinteger2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()).simplify(); }// ok
	case Iop_F64toI64U: {return ((Int)a == 0) ? Variable((ULong)((Double)b), m_ctx) : b.fp2uinteger_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<64>()).simplify(); }// ok

	case Iop_I32StoF32: {return ((Int)a == 0) ? Variable((float)((Int)b), m_ctx) : b.integer2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()).simplify(); }//ok
	case Iop_F32toI32S: {return ((Int)a == 0) ? Variable((Int)((float)b), m_ctx) : b.fp2integer_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()).simplify(); }//ok
	case Iop_I32UtoF32: {return((Int)a == 0) ? Variable((float)((UInt)b), m_ctx) : b.uinteger2fp_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()).simplify(); }//ok
	case Iop_F32toI32U: {return ((Int)a == 0) ? Variable((UInt)((float)b), m_ctx) : b.fp2uinteger_bv(translateRM(m_ctx, (IRRoundingMode)a), m_ctx.fpa_sort<32>()).simplify(); }//ok


	case Iop_CmpF64: {
		double da = a;
		double db = b;
		if (da == db) {
			return Variable(0x40, a, 32);
		}
		else if (da < db) {
			return Variable(0x01, a, 32);
		}
		else if (da > db){
			return Variable(0x0, a, 32);
		}
		else {
			return Variable(0x45, a, 32);
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
		return Variable(result, a);
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
		return Variable(result, a);
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
		return Variable(result, a);
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
		return Variable(result, a);
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
		return Variable(result, a);
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
		return Variable(result, a);
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
		return Variable(result, a);
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
		return Variable(result, a);
	}

	case Iop_ShrV128:goto FAILD;

	default:ppIROp(op); vpanic("???wtf??");
	}
	goto FAILD;
dosymbol:
	switch (op) {
		Z3_caseIop(Add, U);
		Z3_caseIop(Sub, U);
		Z3_caseIop(Mul, U);
		Z3_caseIop(And, U);
		Z3_caseIop(Or, U);
		Z3_caseIop(Xor, U);
		Z3_caseIop(Shl, U);
		Z3_caseIop(Shr, U);
		Z3_caseIop(Sar, S);
		Z3_caseIop(ExpCmpNE, U);
		Z3_caseIop(CmpNE, U);
		Z3_caseIop(CmpEQ, U);
		Z3_caseIop(CasCmpEQ, U);
		Z3_caseIop(CasCmpNE, U);

		

	case Iop_CmpLE32U:return Z3Iop_CmpLE<32, 'U'>(a, b);
	case Iop_CmpLE64U:return Z3Iop_CmpLE<64, 'U'>(a, b);
	case Iop_CmpLE32S:return Z3Iop_CmpLE<32, 'S'>(a, b);
	case Iop_CmpLE64S:return Z3Iop_CmpLE<64, 'S'>(a, b);
	case Iop_CmpLT32U:return Z3Iop_CmpLT<32, 'U'>(a, b);
	case Iop_CmpLT64U:return Z3Iop_CmpLT<64, 'U'>(a, b);
	case Iop_CmpLT32S:return Z3Iop_CmpLT<32, 'S'>(a, b);
	case Iop_CmpLT64S:return Z3Iop_CmpLT<64, 'S'>(a, b);

	case Iop_DivU32:return Z3Iop_Div<32, 'U'>(a, b);
	case Iop_DivS32:return Z3Iop_Div<32, 'S'>(a, b);
	case Iop_DivU64:return Z3Iop_Div<64, 'U'>(a, b);
	case Iop_DivS64:return Z3Iop_Div<64, 'S'>(a, b);
	//case Iop_Not1:vassert(a.bitn == 1); return Variable((UChar)((UChar)a ? 0 : 1));
	//case Iop_Not8:vassert(a.bitn == 8); return Variable((UChar)(~(UChar)a));
	//case Iop_Not16:vassert(a.bitn == 16); return Variable((UShort)(~(UShort)a));
	//case Iop_Not32:vassert(a.bitn == 32); return Variable((UInt)(~(UInt)a));
	//case Iop_Not64:vassert(a.bitn == 64); return Variable((ULong)(~(ULong)a));
	/*
	case Iop_NotV128:vassert(a.bitn == 128); return Variable(_mm_not_si128(a));
	case Iop_NotV256:vassert(a.bitn == 256); return Variable(_mm256_not_si256(a));*/
	//case Iop_XorV128:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_xor_si128(a, b));
	//case Iop_XorV256:vassert(a.bitn == 256); vassert(b.bitn == 256); return Variable(_mm256_xor_si256(a, b));
	//case Iop_OrV128:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_or_si128(a, b));
	//case Iop_OrV256:vassert(a.bitn == 256); vassert(b.bitn == 256); return Variable(_mm256_or_si256(a, b));
	//case Iop_AndV128:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_and_si128(a, b));
	//case Iop_AndV256:vassert(a.bitn == 256); vassert(b.bitn == 256); return Variable(_mm256_and_si256(b, a));

	//case Iop_Add8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_add_epi8(a, b));
	//case Iop_Add16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_add_epi16(a, b));
	//case Iop_Add32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_add_epi32(a, b));
	//case Iop_Add64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_add_epi64(a, b));
	//case Iop_Sub8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_sub_epi8(a, b));//psubb xmm1, xmm0
	//case Iop_Sub16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_sub_epi16(a, b));//psubb xmm1, xmm0
	//case Iop_Sub32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_sub_epi32(a, b));
	//case Iop_Sub64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_sub_epi64(a, b));

	case Iop_CmpGT8Ux16: goto FAILD;
	case Iop_CmpGT16Ux8: goto FAILD;
	case Iop_CmpGT32Ux4: goto FAILD;
	case Iop_CmpGT64Ux2: goto FAILD;
	//case Iop_CmpGT8Sx16:return Variable(a, _mm_cmpgt_epi8(a, b));//true
	//case Iop_CmpGT16Sx8:return Variable(_mm_cmpgt_epi16(a, b));//true
	//case Iop_CmpGT32Sx4:return Variable(_mm_cmpgt_epi32(a, b));//true
	//case Iop_CmpGT64Sx2:return Variable(_mm_cmpgt_epi64(a, b));//true
	//case Iop_CmpEQ8x16:return Variable(_mm_cmpeq_epi8(a, b));//ok
	//case Iop_CmpEQ16x8:return Variable(_mm_cmpeq_epi16(a, b));//ok
	//case Iop_CmpEQ32x4:return Variable(_mm_cmpeq_epi32(a, b));//ok
	//case Iop_CmpEQ64x2:return Variable(_mm_cmpeq_epi64(a, b));//ok


	//case Iop_ShlN8x16:vassert(a.bitn == 128); vassert(b.bitn == 8); goto FAILD;
	//case Iop_ShlN16x8:vassert(a.bitn == 128); vassert(b.bitn == 8); return Variable(_mm_slli_epi16(a, (UChar)b));
	//case Iop_ShlN32x4:vassert(a.bitn == 128); vassert(b.bitn == 8); return Variable(_mm_slli_epi32(a, (UChar)b));
	//case Iop_ShlN64x2:vassert(a.bitn == 128); vassert(b.bitn == 8); return Variable(_mm_slli_epi64(a, (UChar)b));
	//case Iop_InterleaveHI8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpackhi_epi8(b, a));//true
	//case Iop_InterleaveHI16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpackhi_epi16(b, a));//true
	//case Iop_InterleaveHI32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpackhi_epi32(b, a));//ir error ,fixed args
	//case Iop_InterleaveHI64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpackhi_epi64(b, a));//ir error ,fixed args

	//case Iop_InterleaveLO8x16:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpacklo_epi8(b, a));
	//case Iop_InterleaveLO16x8:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpacklo_epi16(b, a));
	//case Iop_InterleaveLO32x4:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpacklo_epi32(b, a));//ir error ,fixed args
	//case Iop_InterleaveLO64x2:vassert(a.bitn == 128); vassert(b.bitn == 128); return Variable(_mm_unpacklo_epi64(b, a));//ir error ,fixed args

	case Iop_8HLto16:vassert(a.bitn == 8); vassert(b.bitn == 8); return Variable(a,Z3_mk_concat(a, a, b), 16);
	case Iop_16HLto32:vassert(a.bitn == 16); vassert(b.bitn == 16); return Variable(a, Z3_mk_concat(a, a, b), 32);
	case Iop_32HLto64:vassert(a.bitn == 32); vassert(b.bitn == 32); return Variable(a, Z3_mk_concat(a, a, b), 64);
	case Iop_64HLto128: 
	case Iop_64HLtoV128: vassert(a.bitn == 64); vassert(b.bitn == 64); return Variable(a, Z3_mk_concat(a, a, b), 128);

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
		return Variable(m_ctx,
			ite(expr(m_ctx, Z3_mk_fpa_eq(a, a, b)),
				m_ctx.bv_val(0x40, 32),
				ite(expr(m_ctx, Z3_mk_fpa_lt(a, a, b)),
					m_ctx.bv_val(0x01, 32),
					ite(expr(m_ctx, Z3_mk_fpa_gt(a, a, b)),
						m_ctx.bv_val(0x00, 32),
						m_ctx.bv_val(0x45, 32)
					)
				)
			), 32);
	}
	case Iop_DivModU128to64: {//ok
		vassert(a.bitn == 128);
		vassert(b.bitn == 64);
		Variable beichushu = b.zext(64);
		return Variable(a,
			Z3_mk_concat(a,
			(a % beichushu).extract(63, 0),
				(a / beichushu).extract(63, 0)
			), 128);
	}
	case Iop_DivModS128to64: {//ok
		vassert(a.bitn == 128);
		vassert(b.bitn == 64);
		Variable beichushu = b.zext(64);
		
		return Variable(a,
			Z3_mk_concat(a,
			(a % beichushu).extract(63, 0) - ite(lt(a, 0), b, Variable(0ull, m_ctx, 64)),
				expr(m_ctx, Z3_mk_bvsdiv(a, a, beichushu)).extract(63, 0)
			), 128);
	}
	case Iop_DivModU64to32: {
		vassert(a.bitn == 64);
		vassert(b.bitn == 32);
		Variable beichushu = b.zext(32);
		return Variable(a,
			Z3_mk_concat(a,
			(a % beichushu).extract(31, 0),
				(a / beichushu).extract(31, 0)
			), 64);
	}

	case Iop_DivModS64to32: {
		vassert(a.bitn == 64);
		vassert(b.bitn == 32);
		Variable beichushu = b.zext(32);
		return Variable(a,
			Z3_mk_concat(a,
			(a % beichushu).extract(31, 0) - ite(lt(a, 0), b, Variable(0ull, m_ctx, 32)),
				Variable(m_ctx, Z3_mk_bvsdiv(a, a, beichushu), 64).extract(31, 0)
			), 64);
	}


	case Iop_ShrV128:goto FAILD;

	


	default:ppIROp(op); vpanic("???wtf??");
	}

FAILD:
	ppIROp(op);
	vpanic("tIRType");

}
