#include "instopt/engine/op_header.h"
 /* ---------------------------------------------------------------------------------------
  *      Notify-bibi Symbolic-Emulation-Engine project
  *      Copyright (c) 2019 Microsoft Corporation by notify-bibi@github, 2496424084@qq.com
  *      ALL RIGHTS RESERVED.
  *
  *      快速地执行 IR operator 并返回
  *      如果是你需要的op code，请帮我完善还未能实现的 IR op
  * ---------------------------------------------------------------------------------------
  */


#define Z3caseIop(IROPNAME, issigned, nb, OP)\
case Iop_##IROPNAME##nb: {																			\
	return a.tos<issigned, nb, Z3_BV_SORT>() OP b.tos<issigned, nb, Z3_BV_SORT>();						\
}

#define Z3caseIopNS(IROPNAME, issigned, nb, append, OP)\
case Iop_##IROPNAME##nb##append: {																	\
	return a.tos<issigned, nb, Z3_BV_SORT>() OP b.tos<issigned, nb, Z3_BV_SORT>();						\
}																								    



#define Z3caseIop_shift(IROPNAME, issigned, nb, OP)\
case Iop_##IROPNAME##nb: {																			\
	return a.tos<issigned, nb, Z3_BV_SORT>() OP b.tos<false, 8, Z3_BV_SORT>();							\
}	


#define Z3caseIop_Arithmetic(IROPNAME, issigned, OP)\
Z3caseIop(IROPNAME, issigned, 8, OP)\
Z3caseIop(IROPNAME, issigned, 16, OP)\
Z3caseIop(IROPNAME, issigned, 32, OP)\
Z3caseIop(IROPNAME, issigned, 64, OP)


#define caseIopNS(IROPNAME, type, nb, append, OP)\
case Iop_##IROPNAME##nb##append: {																	\
	dassert(a.nbits() == nb); 																		\
	dassert(b.nbits() == nb);																		\
	return (rcval<type>&)a OP (rcval<type>&)b;										                \
}																								    


//++++++++++++++++++++++++++++++++++++++++++++++++++


#define caseIop(IROPNAME, type, nb, OP)\
case Iop_##IROPNAME##nb: {\
	dassert(a.nbits() == nb);\
	dassert(b.nbits() == nb);\
	return (rcval<type>&)a OP (rcval<type>&)b;\
}


#define caseIop_Arithmetic(IROPNAME, OP)\
caseIop(IROPNAME, uint8_t , 8, OP)\
caseIop(IROPNAME, uint16_t, 16, OP)\
caseIop(IROPNAME, uint32_t  , 32, OP)\
caseIop(IROPNAME, uint64_t , 64, OP)


#define caseIop_shift(IROPNAME, type, nb, OP)\
case Iop_##IROPNAME##nb: {																			\
	return (rcval<type>&)a OP (rcval<uint8_t>&)b;										            \
}	



#include "instopt/engine/basic_var.hpp"

sv::tval tBinop(IROp op, sv::tval const& a, sv::tval const& b){
    if (a.symb() || b.symb()){
        switch (op) {
            Z3caseIop_Arithmetic(Add, false, +);
            Z3caseIop_Arithmetic(Sub, false, -);
            Z3caseIop_Arithmetic(Mul, false, *);
            Z3caseIop(And, false, 1, & )
            Z3caseIop_Arithmetic(And, false, &);
            Z3caseIop(Or, false, 1, | )
            Z3caseIop_Arithmetic(Or , false, | );
            Z3caseIop_Arithmetic(Xor, false, ^);

            Z3caseIop(DivU, false, 32, / );
            Z3caseIop(DivU, false, 64, / );
            Z3caseIop(DivS, true, 32, / );
            Z3caseIop(DivS, true, 64, / );


            Z3caseIop_shift(Shl, false, 8,  << );
            Z3caseIop_shift(Shl, false, 16, << );
            Z3caseIop_shift(Shl, false, 32, << );
            Z3caseIop_shift(Shl, false, 64, << );


            Z3caseIop_shift(Shr, false, 8,  >> );
            Z3caseIop_shift(Shr, false, 16, >> );
            Z3caseIop_shift(Shr, false, 32, >> );
            Z3caseIop_shift(Shr, false, 64, >> );


            Z3caseIop_shift(Sar, true, 8, >> );
            Z3caseIop_shift(Sar, true, 16, >> );
            Z3caseIop_shift(Sar, true, 32, >> );
            Z3caseIop_shift(Sar, true, 64, >> );


            Z3caseIop_Arithmetic(ExpCmpNE, false, != );
            Z3caseIop_Arithmetic(CasCmpNE, false, != );
            Z3caseIop_Arithmetic(CmpNE, false, != );
            Z3caseIop_Arithmetic(CasCmpEQ, false, == );
            Z3caseIop_Arithmetic(CmpEQ, false, == );

            Z3caseIopNS(CmpLE, false, 32, U, <= );
            Z3caseIopNS(CmpLE, false, 64, U, <= );
            Z3caseIopNS(CmpLE, true, 32, S, <= );
            Z3caseIopNS(CmpLE, true, 64, S, <= );

            Z3caseIopNS(CmpLT, true, 32, S, < );
            Z3caseIopNS(CmpLT, true, 64, S, < );
            Z3caseIopNS(CmpLT, false, 32, U, < );
            Z3caseIopNS(CmpLT, false, 64, U, < );


            case Iop_8HLto16:dassert(a.nbits() == 8); dassert(b.nbits() == 8); return concat((subval<8>&)a, (subval<8>&)b);
            case Iop_16HLto32:dassert(a.nbits() == 16); dassert(b.nbits() == 16); return concat((subval<16>&)a, (subval<16>&)b);
            case Iop_32HLto64:dassert(a.nbits() == 32); dassert(b.nbits() == 32); return concat((subval<32>&)a, (subval<32>&)b);
            case Iop_64HLto128:
            case Iop_64HLtoV128: dassert(a.nbits() == 64); dassert(b.nbits() == 64); return concat((subval<64>&)a, (subval<64>&)b);



            case Iop_ReinterpF64asI64:
            case Iop_ReinterpI64asF64:
            case Iop_ReinterpF32asI32:
            case Iop_ReinterpI32asF32:

            case Iop_F64toI16S: { return ((sfpval<64>&)b).toInteger_sbv<16>(sv::fpRM(a, atorm)); }//ok
            case Iop_F64toI32S: { return ((sfpval<64>&)b).toInteger_sbv<32>(sv::fpRM(a, atorm)); }//ok
            case Iop_F64toI32U: { return ((sfpval<64>&)b).toInteger_ubv<32>(sv::fpRM(a, atorm)); }//ok
            case Iop_F64toI64S: { return ((sfpval<64>&)b).toInteger_sbv<64>(sv::fpRM(a, atorm)); }//ok
            case Iop_F64toI64U: { return ((sfpval<64>&)b).toInteger_ubv<64>(sv::fpRM(a, atorm)); }//ok

            case Iop_I32StoF64: { return ((ssbval<32>&)b).Integer2fpa<11, 53>(sv::fpRM(a, atorm)); }//ok
            case Iop_I32UtoF64: { return ((subval<32>&)b).Integer2fpa<11, 53>(sv::fpRM(a, atorm)); }//ok
            case Iop_I64StoF64: { return ((ssbval<64>&)b).Integer2fpa<11, 53>(sv::fpRM(a, atorm)); }//ok
            case Iop_I64UtoF64: { return ((subval<64>&)b).Integer2fpa<11, 53>(sv::fpRM(a, atorm)); }//ok

            case Iop_I32StoF32: { return ((ssbval<32>&)b).Integer2fpa<8, 24>(sv::fpRM(a, atorm)); }//ok
            case Iop_I32UtoF32: { return ((subval<32>&)b).Integer2fpa<8, 24>(sv::fpRM(a, atorm)); }//ok
            case Iop_I64StoF32: { return ((ssbval<64>&)b).Integer2fpa<8, 24>(sv::fpRM(a, atorm)); }//ok
            case Iop_I64UtoF32: { return ((subval<64>&)b).Integer2fpa<8, 24>(sv::fpRM(a, atorm)); }//ok

            case Iop_F32toI32S: { return ((sfpval<32>&)b).toInteger_sbv<32>(sv::fpRM(a, atorm)); }//ok
            case Iop_F32toI32U: { return ((sfpval<32>&)b).toInteger_ubv<32>(sv::fpRM(a, atorm)); }//ok
            case Iop_F32toI64S: { return ((sfpval<32>&)b).toInteger_sbv<64>(sv::fpRM(a, atorm)); }//ok
            case Iop_F32toI64U: { return ((sfpval<32>&)b).toInteger_ubv<64>(sv::fpRM(a, atorm)); }//ok

            case Iop_F64toF32: { return ((sfpval<64>&)b).fpa2fpa<8, 24>(sv::fpRM(a, atorm)); }
            case Iop_F32toF64: { return ((sfpval<32>&)b).fpa2fpa<11, 53>(sv::fpRM(a, atorm)); }



            case Iop_CmpF128: {
                sfpval<128>& fa = (sfpval<128>&)a;
                sfpval<128>& fb = (sfpval<128>&)b;
                return ite(fa == fb, subval<32>(a, 0x40),
                    ite(fa < fb, subval<32>(a, 0x01),
                        ite(fa > fb, subval<32>(a, 0x00), subval<32>(a, 0x45))
                    )
                );
            }
            case Iop_CmpF64: {
                sfpval<64>& fa = (sfpval<64>&)a;
                sfpval<64>& fb = (sfpval<64>&)b;
                return ite(fa == fb, subval<32>(a, 0x40),
                            ite(fa < fb, subval<32>(a, 0x01),
                                ite(fa > fb, subval<32>(a, 0x00), subval<32>(a, 0x45) )
                                )
                            );
            }
            case Iop_CmpF32: {
                sfpval<32>& fa = (sfpval<32>&)a;
                sfpval<32>& fb = (sfpval<32>&)b;
                return ite(fa == fb, subval<32>(a, 0x40),
                    ite(fa < fb, subval<32>(a, 0x01),
                        ite(fa > fb, subval<32>(a, 0x00), subval<32>(a, 0x45))
                    )
                );
            }
            case Iop_DivModU128to64: {//ok
                dassert(a.nbits() == 128); dassert(b.nbits() == 64);
                auto hi = ((subval<128>&)a % (subval<64>&)b).extract<63, 0>();
                auto lo = ((subval<128>&)a / (subval<64>&)b).extract<63, 0>();
                return concat(hi, lo);
            }
            case Iop_DivModS128to64: {//ok
                dassert(a.nbits() == 128); dassert(b.nbits() == 64);
                auto hi = ((ssbval<128>&)a % (ssbval<64>&)b).extract<63, 0>();
                auto lo = ((ssbval<128>&)a / (ssbval<64>&)b).extract<63, 0>();
                return concat(hi, lo);
            }
            case Iop_DivModU64to32: {
                dassert(a.nbits() == 64); dassert(b.nbits() == 32);
                auto hi = ((subval<64>&)a % (subval<32>&)b).extract<31, 0>();
                auto lo = ((subval<64>&)a / (subval<32>&)b).extract<31, 0>();
                return concat(hi, lo);

            }
            case Iop_DivModS64to32: {
                dassert(a.nbits() == 64); dassert(b.nbits() == 32);
                auto hi = ((ssbval<64>&)a % (ssbval<32>&)b).extract<31, 0>();
                auto lo = ((ssbval<64>&)a / (ssbval<32>&)b).extract<31, 0>();
                return concat(hi, lo);

            }
            case Iop_MullU32: {
                dassert(a.nbits() == 32); dassert(b.nbits() == 32);
                return ((subval<32>&)a).ext<false, 32>() * ((subval<32>&)b).ext<false, 32>();
            }
            case Iop_MullS32: {
                dassert(a.nbits() == 32); dassert(b.nbits() == 32);
                return ((ssbval<32>&)a).ext<true, 32>() * ((ssbval<32>&)b).ext<true, 32>();
            }

#define BNxN(bits, op, N, Mask1, Mask2)\
{   \
    subval<N*bits>& m1 = (subval<N*bits>&)a;\
    subval<N*bits>& m2 = (subval<N*bits>&)b;\
    sv::tval r = ite(m1.extract<bits-1, 0>() op m2.extract<bits-1, 0>(), subval<bits>(a, Mask1), subval<bits>(a, Mask2));\
    for (UInt i = 1; i < N; i++) {\
        sv::tval t = ite(m1.extract<bits>(i) op m2.extract<bits>(i), subval<bits>(a, Mask1), subval<bits>(a, Mask2));\
        r = concat(t, r);\
    }\
    return r;\
}
        case Iop_CmpEQ8x32: BNxN(8 , == , 32, (uint8_t )-1, (uint8_t)0x0);
        case Iop_CmpEQ16x16:BNxN(16, == , 16, (uint16_t)-1, (uint8_t)0x0);
        case Iop_CmpEQ32x8: BNxN(32, == , 8 , (uint32_t)-1, (uint8_t)0x0);
        case Iop_CmpEQ64x4: BNxN(64, == , 4 , (uint64_t)-1, (uint8_t)0x0);

        case Iop_CmpEQ8x16: BNxN(8 , == , 16, (uint8_t )-1, (uint8_t)0x0);
        case Iop_CmpEQ16x8: BNxN(16, == , 8 , (uint16_t)-1, (uint8_t)0x0);
        case Iop_CmpEQ32x4: BNxN(32, == , 4 , (uint32_t)-1, (uint8_t)0x0);
        case Iop_CmpEQ64x2: BNxN(64, == , 2 , (uint64_t)-1, (uint8_t)0x0);

        };
    }else {

	    switch (op) {
	    caseIop_Arithmetic(Add, +);
	    caseIop_Arithmetic(Sub, -);
	    caseIop_Arithmetic(Mul, *);
        caseIop_Arithmetic(And, &);
        case Iop_And1: {  return (sv::ctype_val<false, 1>&)a & (sv::ctype_val<false, 1>&)b;  }
        caseIop_Arithmetic(Or , |);
        case Iop_Or1: {  return (sv::ctype_val<false, 1>&)a | (sv::ctype_val<false, 1>&)b;  }
        caseIop_Arithmetic(Xor, ^);

        caseIop(DivU, uint32_t,  32, / );
        caseIop(DivU, uint64_t, 64, / );
        caseIop(DivS, int32_t,  32, / );
        caseIop(DivS, int64_t, 64, / );



        caseIop_shift(Shl, uint8_t , 8, << );
        caseIop_shift(Shl, uint16_t, 16, << );
        caseIop_shift(Shl, uint32_t  , 32, << );
        caseIop_shift(Shl, uint64_t , 64, << );


        caseIop_shift(Shr, uint8_t , 8, >> );
        caseIop_shift(Shr, uint16_t, 16, >> );
        caseIop_shift(Shr, uint32_t  , 32, >> );
        caseIop_shift(Shr, uint64_t , 64, >> );


        caseIop_shift(Sar, int8_t , 8, >> );
        caseIop_shift(Sar, int16_t, 16, >> );
        caseIop_shift(Sar, int32_t  , 32, >> );
        caseIop_shift(Sar, int64_t , 64, >> );



        caseIop_Arithmetic(ExpCmpNE, != );
        caseIop_Arithmetic(CasCmpNE, != );
        caseIop_Arithmetic(CmpNE, != );
        caseIop_Arithmetic(CasCmpEQ, == );
        caseIop_Arithmetic(CmpEQ, == );

        caseIopNS(CmpLE, uint32_t , 32, U, <= );
        caseIopNS(CmpLE, uint64_t, 64, U, <= );
        caseIopNS(CmpLE, int32_t,  32, S, <= );
        caseIopNS(CmpLE, int64_t, 64, S, <= );

        caseIopNS(CmpLT, uint32_t , 32, U, < );
        caseIopNS(CmpLT, uint64_t, 64, U, < );
        caseIopNS(CmpLT, int32_t  , 32, S, < );
        caseIopNS(CmpLT, int64_t , 64, S, < );

        case Iop_XorV128: {dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_xor_si128(ato(__m128i), bto(__m128i))); }
        case Iop_XorV256: {dassert(a.nbits() == 256); dassert(b.nbits() == 256); return sv::tval(a, _mm256_xor_si256(ato(__m256i), bto(__m256i))); }
        case Iop_OrV128: {dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_or_si128(ato(__m128i), bto(__m128i))); }//ok por     xmm2, xmm3
        case Iop_OrV256: {dassert(a.nbits() == 256); dassert(b.nbits() == 256); return sv::tval(a, _mm256_or_si256(ato(__m256i), bto(__m256i))); }//ok
        case Iop_AndV128: {dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_and_pd(ato(__m128d), bto(__m128d))); }///ok andpd
        case Iop_AndV256: {dassert(a.nbits() == 256); dassert(b.nbits() == 256); return sv::tval(a, _mm256_and_pd(ato(__m256d), bto(__m256d))); }//ok

        case Iop_Add8x16: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_add_epi8(ato(__m128i), bto(__m128i)));  };
        case Iop_Add16x8: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_add_epi16(ato(__m128i), bto(__m128i))); };
        case Iop_Add32x4: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_add_epi32(ato(__m128i), bto(__m128i))); };
        case Iop_Add64x2: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_add_epi64(ato(__m128i), bto(__m128i))); };
        case Iop_Sub8x16: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_sub_epi8(ato(__m128i), bto(__m128i)));  };//ok psubb xmm1, xmm0
        case Iop_Sub16x8: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_sub_epi16(ato(__m128i), bto(__m128i))); };//ok psubb xmm1, xmm0
        case Iop_Sub32x4: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_sub_epi32(ato(__m128i), bto(__m128i))); };//ok
        case Iop_Sub64x2: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_sub_epi64(ato(__m128i), bto(__m128i))); };//ok

	    case Iop_Min8Ux16:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_min_epu8(ato(__m128i), bto(__m128i)));  }//ok pminub  xmm0, xmm1
	    case Iop_Min16Ux8:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_min_epu16(ato(__m128i), bto(__m128i))); }//ok
	    case Iop_Min32Ux4:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_min_epu32(ato(__m128i), bto(__m128i))); }//ok
	    //case Iop_Min64Ux2:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_min_epu64(ato(__m128i), bto(__m128i))); }//ok

        case Iop_CmpEQ64F0x2: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_cmpeq_sd(ato(__m128d), bto(__m128d))); }
        case Iop_CmpLT64F0x2: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_cmplt_sd(ato(__m128d), bto(__m128d))); }
        case Iop_CmpLE64F0x2: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_cmple_sd(ato(__m128d), bto(__m128d))); }
        case Iop_CmpUN64F0x2: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_cmpunord_pd(ato(__m128d), bto(__m128d))); }
		
	    case Iop_Add64F0x2:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_add_sd(ato(__m128d), bto(__m128d))); }//ok addsd   xmm2, xmm0
	    case Iop_Sub64F0x2:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_sub_sd(ato(__m128d), bto(__m128d))); }//ok subsd   xmm2, xmm0
	    case Iop_Mul64F0x2:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_mul_sd(ato(__m128d), bto(__m128d))); }
	    case Iop_Div64F0x2:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_div_sd(ato(__m128d), bto(__m128d))); }
	    case Iop_Max64F0x2:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_max_sd(ato(__m128d), bto(__m128d))); }
	    case Iop_Min64F0x2:{ dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_min_sd(ato(__m128d), bto(__m128d))); }

		

	    case Iop_CmpGT8Ux16: 
	    case Iop_CmpGT16Ux8: 
	    case Iop_CmpGT32Ux4: 
	    case Iop_CmpGT64Ux2: goto FAILD;

        case Iop_CmpGT8Sx16: { return sv::tval(a, _mm_cmpgt_epi8(ato(__m128i), bto(__m128i))); }//true
        case Iop_CmpGT16Sx8: { return sv::tval(a, _mm_cmpgt_epi16(ato(__m128i), bto(__m128i))); }//true
        case Iop_CmpGT32Sx4: { return sv::tval(a, _mm_cmpgt_epi32(ato(__m128i), bto(__m128i))); }//true
        case Iop_CmpGT64Sx2: { return sv::tval(a, _mm_cmpgt_epi64(ato(__m128i), bto(__m128i))); }//true
        case Iop_CmpEQ8x16: { return sv::tval(a, _mm_cmpeq_epi8(ato(__m128i), bto(__m128i))); }//ok  pcmpeqb
        case Iop_CmpEQ16x8: { return sv::tval(a, _mm_cmpeq_epi16(ato(__m128i), bto(__m128i))); }//ok
        case Iop_CmpEQ32x4: { return sv::tval(a, _mm_cmpeq_epi32(ato(__m128i), bto(__m128i))); }//ok
        case Iop_CmpEQ64x2: { return sv::tval(a, _mm_cmpeq_epi64(ato(__m128i), bto(__m128i))); }//ok

	    case Iop_CmpEQ8x32:return sv::tval(a, _mm256_cmpeq_epi8(ato(__m256i), bto(__m256i)));//ok
	    case Iop_CmpEQ16x16:return sv::tval(a, _mm256_cmpeq_epi16(ato(__m256i), bto(__m256i)));//ok
	    case Iop_CmpEQ32x8:return sv::tval(a, _mm256_cmpeq_epi32(ato(__m256i), bto(__m256i)));//ok
	    case Iop_CmpEQ64x4:return sv::tval(a, _mm256_cmpeq_epi64(ato(__m256i), bto(__m256i)));//ok

        case Iop_PermOrZero8x16: {dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_shuffle_epi8(ato(__m128i), bto(__m128i))); }//ok pshufb mm, mm

	    case Iop_ShlN8x16:dassert(a.nbits() == 128); dassert(b.nbits() == 8); goto FAILD;
	    case Iop_ShlN16x8:dassert(a.nbits() == 128); dassert(b.nbits() == 8); return sv::tval(a, _mm_slli_epi16(ato(__m128i), (int8_t&)b));
	    case Iop_ShlN32x4:dassert(a.nbits() == 128); dassert(b.nbits() == 8); return sv::tval(a, _mm_slli_epi32(ato(__m128i), (int8_t&)b));
	    case Iop_ShlN64x2:dassert(a.nbits() == 128); dassert(b.nbits() == 8); return sv::tval(a, _mm_slli_epi64(ato(__m128i), (int8_t&)b));
        case Iop_InterleaveHI8x16: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_unpackhi_epi8(bto(__m128i), ato(__m128i))); }//true
	    case Iop_InterleaveHI16x8: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_unpackhi_epi16(bto(__m128i), ato(__m128i))); }//true
	    case Iop_InterleaveHI32x4: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_unpackhi_epi32(bto(__m128i), ato(__m128i))); }//ir error ,fixed args
	    case Iop_InterleaveHI64x2: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_unpackhi_epi64(bto(__m128i), ato(__m128i))); }//ir error ,fixed args
        case Iop_InterleaveLO8x16: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_unpacklo_epi8(bto(__m128i), ato(__m128i))); }//true
	    case Iop_InterleaveLO16x8: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_unpacklo_epi16(bto(__m128i), ato(__m128i))); }//true
	    case Iop_InterleaveLO32x4: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_unpacklo_epi32(bto(__m128i), ato(__m128i))); }//ir error ,fixed args
	    case Iop_InterleaveLO64x2: { dassert(a.nbits() == 128); dassert(b.nbits() == 128); return sv::tval(a, _mm_unpacklo_epi64(bto(__m128i), ato(__m128i))); }//ir error ,fixed args

        case Iop_8HLto16: { dassert(a.nbits() == 8); dassert(b.nbits() == 8); return sv::tval(a, (UShort)(((UShort)(UChar)ato(UChar) << 8) | (UChar)bto(UChar))); }
        case Iop_16HLto32: { dassert(a.nbits() == 16); dassert(b.nbits() == 16); return sv::tval(a, (UInt)((((UInt)(UShort)ato(UShort)) << 16) | (UShort)bto(UShort))); }
        case Iop_32HLto64: { dassert(a.nbits() == 32); dassert(b.nbits() == 32); return sv::tval(a, (ULong)((((ULong)(UInt)ato(UInt)) << 32) | (UInt)bto(UInt))); }
        case Iop_64HLto128: { return sv::tval(a, _mm_set_epi64x(ato(long long), bto(long long))); }//ok
        case Iop_64HLtoV128: { return sv::tval(a, _mm_set_epi64x(ato(long long), bto(long long))); }//ok


        case Iop_F64toI16S: { return ((Int)ato(Int) == 0) ? sv::tval(a, (int16_t)(double)bto(double)) : sv::tval(((sfpval<64>&)b).toInteger_sbv<16>(sv::fpRM(a, atorm))); }//ok
        case Iop_F64toI32S: { return ((Int)ato(Int) == 0) ? sv::tval(a, (int32_t)(double)bto(double)) : sv::tval(((sfpval<64>&)b).toInteger_sbv<32>(sv::fpRM(a, atorm))); }//ok
        case Iop_F64toI32U: { return ((Int)ato(Int) == 0) ? sv::tval(a, (uint32_t)(double)bto(double)) : sv::tval(((sfpval<64>&)b).toInteger_ubv<32>(sv::fpRM(a, atorm))); }//ok
        case Iop_F64toI64S: { return ((Int)ato(Int) == 0) ? sv::tval(a, (int64_t)(double)bto(double)) : sv::tval(((sfpval<64>&)b).toInteger_sbv<64>(sv::fpRM(a, atorm))); }//ok
        case Iop_F64toI64U: { return ((Int)ato(Int) == 0) ? sv::tval(a, (uint64_t)(double)bto(double)) : sv::tval(((sfpval<64>&)b).toInteger_ubv<64>(sv::fpRM(a, atorm))); }//ok

        case Iop_I32StoF64: { return ((Int)ato(Int) == 0) ? sv::tval(a, (double)(int32_t)bto(int32_t)) : sv::tval(((ssbval<32>&)b).Integer2fpa<11, 53>(sv::fpRM(a, atorm))); }//ok
        case Iop_I32UtoF64: { return ((Int)ato(Int) == 0) ? sv::tval(a, (double)(uint32_t)bto(uint32_t)) : sv::tval(((subval<32>&)b).Integer2fpa<11, 53>(sv::fpRM(a, atorm))); }//ok
        case Iop_I64StoF64: { return ((Int)ato(Int) == 0) ? sv::tval(a, (double)(int64_t)bto(int64_t)) : sv::tval(((ssbval<64>&)b).Integer2fpa<11, 53>(sv::fpRM(a, atorm))); }//ok
        case Iop_I64UtoF64: { return ((Int)ato(Int) == 0) ? sv::tval(a, (double)(uint64_t)bto(uint64_t)) : sv::tval(((subval<64>&)b).Integer2fpa<11, 53>(sv::fpRM(a, atorm))); }//ok

        case Iop_I32StoF32: { return ((Int)ato(Int) == 0) ? sv::tval(a, (float)(int32_t)bto(int32_t)) : sv::tval(((ssbval<32>&)b).Integer2fpa<8, 24>(sv::fpRM(a, atorm))); }//ok
        case Iop_I32UtoF32: { return ((Int)ato(Int) == 0) ? sv::tval(a, (float)(uint32_t)bto(uint32_t)) : sv::tval(((subval<32>&)b).Integer2fpa<8, 24>(sv::fpRM(a, atorm))); }//ok
        case Iop_I64StoF32: { return ((Int)ato(Int) == 0) ? sv::tval(a, (float)(int64_t)bto(int64_t)) : sv::tval(((ssbval<64>&)b).Integer2fpa<8, 24>(sv::fpRM(a, atorm))); }//ok
        case Iop_I64UtoF32: { return ((Int)ato(Int) == 0) ? sv::tval(a, (float)(uint64_t)bto(uint64_t)) : sv::tval(((subval<64>&)b).Integer2fpa<8, 24>(sv::fpRM(a, atorm))); }//ok

        case Iop_F32toI32S: { return ((Int)ato(Int) == 0) ? sv::tval(a, (int32_t)(float)bto(float)) : sv::tval(((sfpval<32>&)b).toInteger_sbv<32>(sv::fpRM(a, atorm))); }//ok
        case Iop_F32toI32U: { return ((Int)ato(Int) == 0) ? sv::tval(a, (uint32_t)(float)bto(float)) : sv::tval(((sfpval<32>&)b).toInteger_ubv<32>(sv::fpRM(a, atorm))); }//ok
        case Iop_F32toI64S: { return ((Int)ato(Int) == 0) ? sv::tval(a, (int64_t)(float)bto(float)) : sv::tval(((sfpval<32>&)b).toInteger_sbv<64>(sv::fpRM(a, atorm))); }//ok
        case Iop_F32toI64U: { return ((Int)ato(Int) == 0) ? sv::tval(a, (uint64_t)(float)bto(float)) : sv::tval(((sfpval<32>&)b).toInteger_ubv<64>(sv::fpRM(a, atorm))); }//ok

        case Iop_F64toF32: { return ((Int)ato(Int) == 0) ? sv::tval(a, (float)(double)bto(double)) : sv::tval(((sfpval<64>&)b).fpa2fpa<8, 24>(sv::fpRM(a, atorm)).simplify()); }
        case Iop_F32toF64: { return ((Int)ato(Int) == 0) ? sv::tval(a, (double)(float)bto(float)) : sv::tval(((sfpval<32>&)b).fpa2fpa<11, 53>(sv::fpRM(a, atorm)).simplify()); }

	    case Iop_CmpF64: {
		    double da = ato(double);
		    double db = bto(double);
		    if (da == db) {
			    return sv::tval(a, 0x40u);
		    }
		    else if (da < db) {
			    return sv::tval(a, 0x01u);
		    }
		    else if (da > db){
			    return sv::tval(a, 0x0u);
		    }
		    else {
			    return sv::tval(a, 0x45u);
		    }
	    }

        case Iop_CmpF32: {
            float da = ato(float);
            float db = bto(float);
            if (da == db) {
                return sv::tval(a, 0x40u);
            }
            else if (da < db) {
                return sv::tval(a, 0x01u);
            }
            else if (da > db) {
                return sv::tval(a, 0x0u);
            }
            else {
                return sv::tval(a, 0x45u);
            }
        }
	    case Iop_DivModS64to32: {
            dassert(a.nbits() == 64); 
            dassert(b.nbits() == 32);
            ULong na = ato(ULong); 
            UInt nb = bto(UInt);
            UInt rem, s;
            __asm__(
                "xor %%rcx,%%rcx;\n\t"
                "mov %[hi32],%%rdx;\n\t"
                "mov %[lo32],%%rax;\n\t"
                "mov %[bcs],%%ecx;\n\t"
                "idiv %%ecx;\n\t"
                "mov %%eax,%[s];\n\t"
                "mov %%edx,%[rem];\n\t"
                : [s]"=r"(s), [rem]"=r"(rem)
                : [hi32] "r"(na >> 32), [lo32] "r"(na & 0xffffffff), [bcs] "r"(nb)
                : "memory", "%rax", "rdx", "rcx"
            );
            ULong re = (((ULong)rem) << 32) | s;
            return sv::tval(a, re);
	    }
	    case Iop_DivModU64to32: {
            dassert(a.nbits() == 64);
            dassert(b.nbits() == 32);
            ULong na = ato(ULong);
            UInt nb = bto(UInt);
            UInt rem, s;
            __asm__(
                "xor %%rcx,%%rcx;\n\t"
                "mov %[hi32],%%rdx;\n\t"
                "mov %[lo32],%%rax;\n\t"
                "mov %[bcs],%%ecx;\n\t"
                "div %%ecx;\n\t"
                "mov %%eax,%[s];\n\t"
                "mov %%edx,%[rem];\n\t"
                : [s] "=r"(s), [rem] "=r"(rem)
                : [hi32] "r"(na >> 32), [lo32] "r"(na & 0xffffffff), [bcs] "r"(nb)
                : "rax", "rdx", "rcx"
            );
            ULong re = (((ULong)rem) << 32) | s;
            return sv::tval(a, re);
	    }
	    case Iop_DivModU128to64: {//ok
		    dassert(a.nbits() == 128); dassert(b.nbits() == 64);
            __m128i na = ato(__m128i); ULong nb = bto(ULong);
            __m128i re;
            __asm__(
                "mov %[hi64],%%rdx;\n\t"
                "mov %[lo64],%%rax;\n\t"
                "mov %[bcs],%%rcx;\n\t"
                "div %%rcx;\n\t"
                "mov %%rax,%[s];\n\t"
                "mov %%rdx,%[rem];\n\t"
                : [s] "=r"(M128i(re).m128i_u64[0]), [rem] "=r"(M128i(re).m128i_u64[1])
                : [hi64] "r"(M128i(na).m128i_u64[1]), [lo64] "r"(M128i(na).m128i_u64[0]), [bcs] "r"(nb)
                : "rax", "rdx", "rcx"
            );
            return sv::tval(a, re);
	    }
	    case Iop_DivModS128to64: {
            dassert(a.nbits() == 128); dassert(b.nbits() == 64);
            __m128i na = ato(__m128i); 
            ULong nb = bto(ULong);
            __m128i re;
            __asm__(
                "mov %[hi64],%%rdx;\n\t"
                "mov %[lo64],%%rax;\n\t"
                "mov %[bcs],%%rcx;\n\t"
                "idiv %%rcx;\n\t"
                "mov %%rax,%[s];\n\t"
                "mov %%rdx,%[rem];\n\t"
                : [s] "=r"(M128i(re).m128i_u64[0]), [rem] "=r"(M128i(re).m128i_u64[1])
                : [hi64] "r"(M128i(na).m128i_u64[1]), [lo64] "r"(M128i(na).m128i_u64[0]), [bcs] "r"(nb)
                : "rax", "rdx", "rcx"
            );
            return sv::tval(a, re);
	    }
        case Iop_MullU32: {
            dassert(a.nbits() == 32); dassert(b.nbits() == 32);
            UInt na = ato(UInt); 
            UInt nb = bto(UInt);
            ULong re;
            __asm__(
                "xor %%rax,%%rax;\n\t"
                "xor %%rbx,%%rbx;\n\t"
                "mov %[a],%%eax;\n\t"
                "mov %[b],%%ebx;\n\t"
                "mul %%ebx;\n\t"
                "mov %%eax,%[lo32];\n\t"
                "mov %%edx,%[hi32];\n\t"
                : [lo32] "=r"(*(UInt*)(&re)), [hi32] "=r"(((UInt*)&re)[1])
                : [a] "r"(na), [b] "r"(nb)
                : "rax", "edx"
            );
            return sv::tval(a, re);
        }
        case Iop_MullS32: {
            dassert(a.nbits() == 32); dassert(b.nbits() == 32);
            UInt na = ato(UInt); 
            UInt nb = bto(UInt);
            ULong re;
            __asm__(
                "xor %%rax,%%rax;\n\t"
                "xor %%rbx,%%rbx;\n\t"
                "mov %[a],%%eax;\n\t"
                "mov %[b],%%ebx;\n\t"
                "imul %%ebx;\n\t"
                "mov %%eax,%[lo32];\n\t"
                "mov %%edx,%[hi32];\n\t"
                : [lo32] "=r"(*(UInt*)(&re)), [hi32] "=r"(((UInt*)&re)[1])
                : [a] "r"(na), [b] "r"(nb)
                : "rax", "edx"
            );
            return sv::tval(a, re);
        }
	    case Iop_MullU64: {
            dassert(a.nbits() == 64); dassert(b.nbits() == 64);
            ULong na = ato(ULong); 
            ULong nb = bto(ULong);
            __m128i re;
            __asm__(
                "mov %[a],%%rax;\n\t"
                "mov %[b],%%rbx;\n\t"
                "mul %%rbx;\n\t"
                "mov %%rax,%[lo64];\n\t"
                "mov %%rdx,%[hi64];\n\t"
                : [lo64] "=r"(M128i(re).m128i_u64[0]), [hi64] "=r"(M128i(re).m128i_u64[1])
                : [a] "r"(na), [b] "r"(nb)
                : "rax", "edx"
            );
            return sv::tval(a, re);
	    }
	    case Iop_MullS64: {
            dassert(a.nbits() == 64); dassert(b.nbits() == 64);
            ULong na = ato(ULong); 
            ULong nb = bto(ULong);
            __m128i re;
            __asm__(
                "mov %[a],%%rax;\n\t"
                "mov %[b],%%rbx;\n\t"
                "imul %%rbx;\n\t"
                "mov %%rax,%[lo64];\n\t"
                "mov %%rdx,%[hi64];\n\t"
                : [lo64]"=r"(M128i(re).m128i_u64[0]), [hi64]"=r"(M128i(re).m128i_u64[1])
                : [a] "r"(na), [b] "r"(nb)
                : "rax", "edx"
            );
            return sv::tval(a, re);
	    }
        };
    }
    
FAILD:
    VPANIC("unsupport ir binop ");
}
