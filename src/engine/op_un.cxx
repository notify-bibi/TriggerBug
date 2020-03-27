#include "engine/op_header.h"
//
//static Vns bsf32(Vns const&s) {
//    Vns re(s, (UChar)32);
//    for (int i = s.bitn - 1; i != -1; i--) {
//        re = ite(s.extract(i, i).toZ3Bool(), Vns(s, (UChar)i), re);
//    }
//    return re.zext(24);
//}
//
//
//template<unsigned nb>
//static ubval<nb> bsr(const ubval<nb>& s) {
//    ubval<nb> r = ubval<nb>(s, nb);
//    for (int i = 0; i < nb; i++) 
//        r = ite(s.extract<1>(i) == 1, ubval<nb>(s, i), r);
//    return r;
//}
//
//template<unsigned nb>
//static ubval<nb> bsf(const ubval<nb>& s) {
//    ubval<nb> r = ubval<nb>(s, nb);
//    for (int i = nb - 1; i != -1; i--) 
//        r = ite(s.extract<1>(i) == 1, ubval<nb>(s, i), r);
//    return r;
//}
//
//static Vns bsr64(Vns const& s) {
//    Vns re(s, (UChar)64);
//    for (int i = 0; i < s.bitn; i++) {
//        re = ite(s.extract(i, i).toZ3Bool(), Vns(s, (UChar)i), re);
//    }
//    return re.zext(56);
//}
//static inline int CountLeadingZeros32(uint32_t n) {
//#if defined(_MSC_VER)
//    unsigned long result = 0;
//    if (_BitScanReverse(&result, n)) {
//        return 31 - result;
//    }
//    return 32;
//#elif defined(__GNUC__)
//    if (n == 0) {
//        return 32;
//    }
//    return __builtin_clz(n);
//#endif
//}
//
//static inline int MostSignificantBit32(uint32_t n) {
//    return 32 - CountLeadingZeros32(n);
//}
//
//static inline int CountLeadingZeros64(uint64_t n) {
//#if defined(_MSC_VER)
//    unsigned long result = 0; 
//    if (_BitScanReverse64(&result, n)) {
//        return 63 - result;
//    }
//    return 64;
//#elif defined(__GNUC__)
//    if (n == 0) {
//        return 64;
//    }
//    return __builtin_clzll(n);
//#endif
//}
//
//static inline int MostSignificantBit64(uint64_t n) {
//    return 64 - CountLeadingZeros64(n);
//}

#define Z3Iop_ZEXT(T1, T2) { return ((ubval<T1>&)a).ext<false, T2>(); }
#define Z3Iop_SEXT(T1, T2) { return ((sbval<T1>&)a).ext<true , T2>(); }


#define Iop_to(T1, T2) { return tval(a, (T2) ato(T1)); }

//tval Kernel::tUnop(IROp op, tval const& a) {
//    //a.tostr();
//    if (a.symb()) {
//        switch (op) {
//        case Iop_1Uto8:  Z3Iop_ZEXT(1, 8);
//        case Iop_1Uto32: Z3Iop_ZEXT(1, 32);
//        case Iop_1Uto64: Z3Iop_ZEXT(1, 64);
//        case Iop_1Sto8:  Z3Iop_SEXT(1, 8);
//        case Iop_1Sto16: Z3Iop_SEXT(1, 16);
//        case Iop_1Sto32: Z3Iop_SEXT(1, 32);
//        case Iop_1Sto64: Z3Iop_SEXT(1, 64);
//
//        case Iop_Not1:  { return ~atou(1); }
//        case Iop_Not8:  { return ~atou(8); }
//        case Iop_Not16: { return ~atou(16);}
//        case Iop_Not32: { return ~atou(32);}
//        case Iop_Not64: { return ~atou(64);}
//
//        case Iop_8Sto16:   Z3Iop_SEXT(8, 16);
//        case Iop_8Sto32:   Z3Iop_SEXT(8, 32);
//        case Iop_8Sto64:   Z3Iop_SEXT(8, 64);
//        case Iop_8Uto16:   Z3Iop_ZEXT(8, 16);
//        case Iop_8Uto32:   Z3Iop_ZEXT(8, 32);
//        case Iop_8Uto64:   Z3Iop_ZEXT(8, 64);
//        case Iop_16Sto32:  Z3Iop_SEXT(16, 32);
//        case Iop_16Sto64:  Z3Iop_SEXT(16, 64);
//        case Iop_16Uto32:  Z3Iop_ZEXT(16, 32);
//        case Iop_16Uto64:  Z3Iop_ZEXT(16, 64);
//        case Iop_32Sto64:  Z3Iop_SEXT(32, 64);
//        case Iop_32Uto64:  Z3Iop_ZEXT(32, 64);
//        case Iop_32UtoV128:Z3Iop_ZEXT(32, 128);
//        case Iop_64UtoV128:Z3Iop_ZEXT(64, 128);
//
//        case Iop_32to1:     { return atou(32 ).extract<0 , 0 >(); }
//        case Iop_64to1:     { return atou(64 ).extract<0 , 0 >(); }
//        case Iop_32to8:     { return atou(32 ).extract<7 , 0 >(); }
//        case Iop_64to8:     { return atou(64 ).extract<7 , 0 >(); }
//        case Iop_64to16:    { return atou(64 ).extract<15, 0 >(); }
//        case Iop_32to16:    { return atou(32 ).extract<15, 0 >(); }
//        case Iop_64to32:    { return atou(64 ).extract<31, 0 >(); }
//        case Iop_V128to32:  { return atou(128).extract<31, 0 >(); }
//        case Iop_V128to64:  { return atou(128).extract<63, 0 >(); }
//        case Iop_128to64:   { return atou(128).extract<63, 0 >(); }
//        case Iop_16HIto8:   { return atou(16 ).extract<15, 8 >(); }
//        case Iop_32HIto16:  { return atou(32 ).extract<31, 16>(); }
//        case Iop_64HIto32:  { return atou(64 ).extract<63, 32>(); }
//        case Iop_128HIto64: { return atou(128).extract<127,64>(); }
//        case Iop_V128HIto64:{ return atou(128).extract<127,64>(); }
//
//        case Iop_Clz32: { return 31 + bsr(atou(32)); }
//        case Iop_Clz64: { return 63 - bsr(atou(64)); }
//        case Iop_Ctz32: { return bsf(atou(32)); }//ok
//        case Iop_Ctz64: { return bsf(atou(64)); }//ok
//
//        case Iop_GetMSBs8x16: {
//            tval r = atou(8 * 16).extract<1>(0);
//            for (UInt i = 1; i < 16; i++)  r = concat(atou(8 * 16).extract<1>(i), r);
//            return r;
//        }
//        };
//
//
//    }else {
//
//        switch (op) {
//        case Iop_1Uto8:  { return tval(a, ( uint8_t)(((uint8_t)(sv::ctype_val<uint8_t, 1>&)a) & 1 ? -1 : 0) ); }
//        case Iop_1Uto32: { return tval(a, (uint32_t)(((uint8_t)(sv::ctype_val<uint8_t, 1>&)a) & 1 ? -1 : 0) ); }
//        case Iop_1Uto64: { return tval(a, (uint64_t)(((uint8_t)(sv::ctype_val<uint8_t, 1>&)a) & 1 ? -1 : 0) ); }
//        case Iop_1Sto8:  { return tval(a, ( int8_t)(((uint8_t)(sv::ctype_val<uint8_t,  1>&)a) & 1 ? -1 : 0) ); }
//        case Iop_1Sto16: { return tval(a, (int16_t)(((uint8_t)(sv::ctype_val<uint8_t,  1>&)a) & 1 ? -1 : 0) ); }
//        case Iop_1Sto32: { return tval(a, (int32_t)(((uint8_t)(sv::ctype_val<uint8_t,  1>&)a) & 1 ? -1 : 0) ); }
//        case Iop_1Sto64: { return tval(a, (int64_t)(((uint8_t)(sv::ctype_val<uint8_t,  1>&)a) & 1 ? -1 : 0) ); }
//
//        case Iop_32to1: { return (sv::ctype_val<uint8_t, 1>&)a; }
//        case Iop_64to1: { return (sv::ctype_val<uint8_t, 1>&)a; }
//
//        case Iop_Not1:    { return ~(sv::ctype_val<uint8_t, 1>&)a; }
//        case Iop_Not8:    { return ~(sv::ctype_val<uint8_t>&)a; }
//        case Iop_Not16:   { return ~(sv::ctype_val<uint16_t>&)a; }
//        case Iop_Not32:   { return ~(sv::ctype_val<uint32_t>&)a; }
//        case Iop_Not64:   { return ~(sv::ctype_val<uint64_t>&)a; }
//        case Iop_NotV128: { return ~(sv::ctype_val<__m128i>&)a; }
//        case Iop_NotV256: { return ~(sv::ctype_val<__m256i>&)a; }
//
//        case Iop_8Sto16: Iop_to(Char, Short);  
//        case Iop_8Sto32: Iop_to(Char, Int);    
//        case Iop_8Sto64: Iop_to(Char, Long);   
//        case Iop_8Uto16: Iop_to(UChar, UShort);
//        case Iop_8Uto32: Iop_to(UChar, UInt);  
//        case Iop_8Uto64: Iop_to(UChar, ULong); 
//
//        case Iop_16Sto32: Iop_to(Short, Int);   
//        case Iop_16Sto64: Iop_to(Short, Long);  
//        case Iop_16Uto32: Iop_to(UShort, UInt); 
//        case Iop_16Uto64: Iop_to(UShort, ULong);
//
//        case Iop_32Sto64:   Iop_to(Int, Long);  
//        case Iop_32Uto64:   Iop_to(UInt, ULong);
//
//
//        case Iop_64to32: Iop_to(ULong, UInt);
//        case Iop_64to16: Iop_to(ULong, UShort);
//        case Iop_64to8 : Iop_to(ULong, UChar);
//        case Iop_32to16: Iop_to(UInt, UShort);
//        case Iop_32to8:  Iop_to(UInt, UChar);
//
//
//        case Iop_V128to32: { return ato(uint32_t); }//OK
//        case Iop_V128to64: { return ato(uint64_t); }//OK
//        case Iop_128to64:  { return ato(uint64_t); }//OK
//        case Iop_V256toV128_0: { return ato(__m128i); }
//        case Iop_V256toV128_1: { return tval(a, ((__m128i*)a.cptr())[1]); };
//
//        case Iop_V128HIto64: { return tval(a, ((uint64_t*)a.cptr())[1]); }//OK
//        case Iop_128HIto64: { return tval(a, ((uint64_t*)a.cptr())[1]); }//OK
//        case Iop_32HIto16: { return tval(a, (uint16_t)((uint32_t)ato(uint32_t) >> 16)); }
//        case Iop_64HIto32: { return tval(a, (uint32_t)((uint64_t)ato(uint64_t) >> 32)); }
//        case Iop_16HIto8: { return tval(a, (uint8_t)((uint16_t)ato(uint16_t) >> 8)); }
//
//        case Iop_32UtoV128: { return tval(a, _mm_set_epi32(0, 0, 0, ato(int32_t))); }
//        case Iop_64UtoV128: { return tval(a, _mm_set_epi64x(0, ato(int64_t))); }
//
//        case Iop_Clz32: { return Vns(a, (uint32_t)CountLeadingZeros32(ato(uint32_t))); }
//        case Iop_Clz64: { return Vns(a, (uint64_t)CountLeadingZeros64(ato(uint64_t)));}
//        case Iop_Ctz32: {
//            unsigned long result = 0;
//            if (!_BitScanForward(&result, ato(uint32_t)))  result = 32;
//            return Vns(a, (uint32_t)result);
//        };//ok
//        case Iop_Ctz64: {
//            unsigned long result = 0;
//            if (!_BitScanForward64(&result, ato(uint64_t)))  result = 64;
//            return Vns(a, (uint64_t)result);
//        };//ok bsf
//        case Iop_GetMSBs8x16: { return Vns(a, (UShort)_mm_movemask_epi8(ato(__m128i))); }//OK pmovmskb
//
//        case Iop_Abs64Fx2:
//        case Iop_Neg64Fx2:
//        case Iop_RSqrtEst64Fx2:
//        case Iop_RecipEst64Fx2:
//
//        case Iop_Sqrt64F0x2:
//
//        case Iop_Sqrt32Fx8:
//        case Iop_RSqrtEst32Fx8:
//        case Iop_RecipEst32Fx8:
//
//        case Iop_Sqrt64Fx4:
//
//        case Iop_RecipEst32Fx4:
//        case Iop_RoundF32x4_RM:
//        case Iop_RoundF32x4_RP:
//        case Iop_RoundF32x4_RN:
//        case Iop_RoundF32x4_RZ:
//        case Iop_RecipEst32Ux4:
//        case Iop_Abs32Fx4:
//        case Iop_Neg32Fx4:
//        case Iop_RSqrtEst32Fx4:
//
//        case Iop_RecipEst32Fx2:
//        case Iop_RecipEst32Ux2:
//        case Iop_Abs32Fx2:
//        case Iop_Neg32Fx2:
//        case Iop_RSqrtEst32Fx2:
//
//        case Iop_Sqrt32F0x4:
//        case Iop_RSqrtEst32F0x4:
//        case Iop_RecipEst32F0x4:
//
//        case Iop_Dup8x16:
//        case Iop_Dup16x8:
//        case Iop_Dup32x4:
//        case Iop_Reverse1sIn8_x16:
//        case Iop_Reverse8sIn16_x8:
//        case Iop_Reverse8sIn32_x4:
//        case Iop_Reverse16sIn32_x4:
//        case Iop_Reverse8sIn64_x2:
//        case Iop_Reverse16sIn64_x2:
//        case Iop_Reverse32sIn64_x2:
//
//        case Iop_ZeroHI64ofV128:
//        case Iop_ZeroHI96ofV128:
//        case Iop_ZeroHI112ofV128:
//        case Iop_ZeroHI120ofV128:
//
//        case Iop_F128HItoF64:  /* F128 -> high half of F128 */
//        case Iop_D128HItoD64:  /* D128 -> high half of D128 */
//        case Iop_F128LOtoF64:  /* F128 -> low  half of F128 */
//        case Iop_D128LOtoD64:  /* D128 -> low  half of D128 */
//
//        case Iop_NegF128:
//        case Iop_AbsF128:
//
//        case Iop_I32StoF128: /* signed I32 -> F128 */
//        case Iop_I64StoF128: /* signed I64 -> F128 */
//        case Iop_I32UtoF128: /* unsigned I32 -> F128 */
//        case Iop_I64UtoF128: /* unsigned I64 -> F128 */
//        case Iop_F32toF128:  /* F32 -> F128 */
//        case Iop_F64toF128:  /* F64 -> F128 */
//        case Iop_I32StoD128: /* signed I64 -> D128 */
//        case Iop_I64StoD128: /* signed I64 -> D128 */
//        case Iop_I32UtoD128: /* unsigned I32 -> D128 */
//        case Iop_I64UtoD128: /* unsigned I64 -> D128 */
//
//        case Iop_NegF64:
//        case Iop_AbsF64:
//        case Iop_RSqrtEst5GoodF64:
//        case Iop_RoundF64toF64_NEAREST:
//        case Iop_RoundF64toF64_NegINF:
//        case Iop_RoundF64toF64_PosINF:
//        case Iop_RoundF64toF64_ZERO:
//        case Iop_D32toD64:
//        case Iop_I32StoD64:
//        case Iop_I32UtoD64:
//        case Iop_ExtractExpD64:    /* D64  -> I64 */
//        case Iop_ExtractExpD128:   /* D128 -> I64 */
//        case Iop_ExtractSigD64:    /* D64  -> I64 */
//        case Iop_ExtractSigD128:   /* D128 -> I64 */
//        case Iop_DPBtoBCD:
//        case Iop_BCDtoDPB:
//
//        case Iop_D64toD128:
//
//        case Iop_TruncF64asF32:
//        case Iop_NegF32:
//        case Iop_AbsF32:
//        case Iop_F16toF32:
//
//        case Iop_Dup8x8:
//        case Iop_Dup16x4:
//        case Iop_Dup32x2:
//        case Iop_Reverse8sIn16_x4:
//        case Iop_Reverse8sIn32_x2:
//        case Iop_Reverse16sIn32_x2:
//        case Iop_Reverse8sIn64_x1:
//        case Iop_Reverse16sIn64_x1:
//        case Iop_Reverse32sIn64_x1:
//        case Iop_V256to64_0: case Iop_V256to64_1:
//        case Iop_V256to64_2: case Iop_V256to64_3:
//
//        case Iop_GetMSBs8x8:
//
//
//        case Iop_ReinterpF64asI64:
//        case Iop_ReinterpI64asF64:
//        case Iop_ReinterpI32asF32:
//        case Iop_ReinterpF32asI32:
//        case Iop_ReinterpI64asD64:
//        case Iop_ReinterpD64asI64:
//
//        case Iop_CmpNEZ8x8:
//        case Iop_Cnt8x8:
//        case Iop_Clz8x8:
//        case Iop_Cls8x8:
//        case Iop_Abs8x8:
//
//        case Iop_CmpNEZ8x16:
//        case Iop_Cnt8x16:
//        case Iop_Clz8x16:
//        case Iop_Cls8x16:
//        case Iop_Abs8x16:
//
//        case Iop_CmpNEZ16x4:
//        case Iop_Clz16x4:
//        case Iop_Cls16x4:
//        case Iop_Abs16x4:
//
//        case Iop_CmpNEZ16x8:
//        case Iop_Clz16x8:
//        case Iop_Cls16x8:
//        case Iop_Abs16x8:
//
//        case Iop_CmpNEZ32x2:
//        case Iop_Clz32x2:
//        case Iop_Cls32x2:
//        case Iop_Abs32x2:
//
//        case Iop_CmpNEZ32x4:
//        case Iop_Clz32x4:
//        case Iop_Cls32x4:
//        case Iop_Abs32x4:
//        case Iop_RSqrtEst32Ux4:
//
//        case Iop_CmpwNEZ32:
//
//        case Iop_CmpwNEZ64:
//
//        case Iop_CmpNEZ64x2:
//        case Iop_CipherSV128:
//        case Iop_Clz64x2:
//        case Iop_Abs64x2:
//
//        case Iop_PwBitMtxXpose64x2:
//
//        case Iop_NarrowUn16to8x8:
//        case Iop_NarrowUn32to16x4:
//        case Iop_NarrowUn64to32x2:
//        case Iop_QNarrowUn16Sto8Sx8:
//        case Iop_QNarrowUn16Sto8Ux8:
//        case Iop_QNarrowUn16Uto8Ux8:
//        case Iop_QNarrowUn32Sto16Sx4:
//        case Iop_QNarrowUn32Sto16Ux4:
//        case Iop_QNarrowUn32Uto16Ux4:
//        case Iop_QNarrowUn64Sto32Sx2:
//        case Iop_QNarrowUn64Sto32Ux2:
//        case Iop_QNarrowUn64Uto32Ux2:
//
//        case Iop_Widen8Sto16x8:
//        case Iop_Widen8Uto16x8:
//        case Iop_Widen16Sto32x4:
//        case Iop_Widen16Uto32x4:
//        case Iop_Widen32Sto64x2:
//        case Iop_Widen32Uto64x2:
//
//        case Iop_PwAddL32Ux2:
//        case Iop_PwAddL32Sx2:
//
//        case Iop_PwAddL16Ux4:
//        case Iop_PwAddL16Sx4:
//
//        case Iop_PwAddL8Ux8:
//        case Iop_PwAddL8Sx8:
//
//        case Iop_PwAddL32Ux4:
//        case Iop_PwAddL32Sx4:
//
//        case Iop_PwAddL16Ux8:
//        case Iop_PwAddL16Sx8:
//
//        case Iop_PwAddL8Ux16:
//        case Iop_PwAddL8Sx16:
//
//        case Iop_I64UtoF32:
//        default:
//            goto FAILD;
//        }
//    }
//FAILD:
//    vex_printf("unsupport Unop: ");
//    ppIROp(op);
//    vpanic("tIRType");
//}
