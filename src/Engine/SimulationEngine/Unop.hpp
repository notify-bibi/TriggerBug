
using namespace z3;


static Vns bsf32(Vns const&s) {
    Vns re(s, (UChar)32);
    for (int i = s.bitn - 1; i != -1; i--) {
        re = ite(s.extract(i, i).toZ3Bool(), Vns(s, (UChar)i), re);
    }
    return re.zext(24);
}

static Vns bsr32(Vns const& s) {
    Vns re(s, (UInt)32);
    for (int i = 0; i < s.bitn; i++) {
        re = ite(s.extract(i, i).toZ3Bool(), Vns(s, (UChar)i), re);
    }
    return re.zext(24);
}

static Vns bsf64(Vns const& s) {
    Vns re(s, (UChar)64);
    for (int i = s.bitn - 1; i != -1; i--) {
        re = ite(s.extract(i, i).toZ3Bool(), Vns(s, (UChar)i), re);
    }
    return re.zext(56);
}

static Vns bsr64(Vns const& s) {
    Vns re(s, (UChar)64);
    for (int i = 0; i < s.bitn; i++) {
        re = ite(s.extract(i, i).toZ3Bool(), Vns(s, (UChar)i), re);
    }
    return re.zext(56);
}
static inline int CountLeadingZeros32(uint32_t n) {
#if defined(_MSC_VER)
    unsigned long result = 0;
    if (_BitScanReverse(&result, n)) {
        return 31 - result;
    }
    return 32;
#elif defined(__GNUC__)
    if (n == 0) {
        return 32;
    }
    return __builtin_clz(n);
#endif
}

static inline int MostSignificantBit32(uint32_t n) {
    return 32 - CountLeadingZeros32(n);
}

static inline int CountLeadingZeros64(uint64_t n) {
#if defined(_MSC_VER)
    unsigned long result = 0; 
    if (_BitScanReverse64(&result, n)) {
        return 63 - result;
    }
    return 64;
#elif defined(__GNUC__)
    if (n == 0) {
        return 64;
    }
    return __builtin_clzll(n);
#endif
}

static inline int MostSignificantBit64(uint64_t n) {
    return 64 - CountLeadingZeros64(n);
}

static inline Z3_ast bool2bv(Z3_context ctx, Z3_ast ast) {
    Z3_inc_ref(ctx, ast);
    Z3_sort sort = Z3_mk_bv_sort(ctx, 1);
    Z3_inc_ref(ctx, (Z3_ast)sort);
    Z3_ast zero = Z3_mk_int(ctx, 0, sort);
    Z3_inc_ref(ctx, zero);
    Z3_ast one = Z3_mk_int(ctx, 1, sort);
    Z3_inc_ref(ctx, one);
    Z3_ast result = Z3_mk_ite(ctx, ast, one, zero);
    Z3_dec_ref(ctx, one);
    Z3_dec_ref(ctx, zero);
    Z3_dec_ref(ctx, ast);
    Z3_dec_ref(ctx, (Z3_ast)sort);
    return result;
}


#define Iop_to(T1, T2)  Vns(a, (T2)(((T1)a)))

#define Iop_ZEXT(T1, T2) Vns(a, Z3_mk_zero_ext(m_ctx, T2 - T1, a), T2)
#define Iop_SEXT(T1, T2) Vns(a, Z3_mk_sign_ext(m_ctx, T2 - T1, a), T2)


inline Vns State::T_Unop(context &m_ctx, IROp op, Vns const& a) {
    //a.tostr();
    if (a.symbolic())
    {
        switch (op) {
        case Iop_1Uto8: return Iop_ZEXT(1, 8);
        case Iop_1Uto32:return Iop_ZEXT(1, 32);
        case Iop_1Uto64:return Iop_ZEXT(1, 64);
        case Iop_1Sto8: return Iop_SEXT(1, 8);
        case Iop_1Sto16:return Iop_SEXT(1, 16);
        case Iop_1Sto32:return Iop_SEXT(1, 32);
        case Iop_1Sto64:return Iop_SEXT(1, 64);

        case Iop_32to1:vassert(a.bitn == 32); return Vns(m_ctx, Z3_mk_extract(m_ctx, 0, 0, a), 1);
        case Iop_64to1:vassert(a.bitn == 64); return Vns(m_ctx, Z3_mk_extract(m_ctx, 0, 0, a), 1);

        case Iop_Not1: return Vns(m_ctx, Z3_mk_bvnot(m_ctx, a), 1);
        case Iop_Not8: return Vns(m_ctx, Z3_mk_bvnot(m_ctx, a), 8);
        case Iop_Not16:return Vns(m_ctx, Z3_mk_bvnot(m_ctx, a), 16);
        case Iop_Not32:return Vns(m_ctx, Z3_mk_bvnot(m_ctx, a), 32);
        case Iop_Not64:return Vns(m_ctx, Z3_mk_bvnot(m_ctx, a), 64);

        case Iop_8Sto16:return Iop_SEXT(8, 16);
        case Iop_8Sto32:return Iop_SEXT(8, 32);
        case Iop_8Sto64:return Iop_SEXT(8, 64);
        case Iop_8Uto16:return Iop_ZEXT(8, 16);
        case Iop_8Uto32:return Iop_ZEXT(8, 32);
        case Iop_8Uto64:return Iop_ZEXT(8, 64);

        case Iop_16Sto32:return Iop_SEXT(16, 32);
        case Iop_16Sto64:return Iop_SEXT(16, 64);
        case Iop_16Uto32:return Iop_ZEXT(16, 32);
        case Iop_16Uto64:return Iop_ZEXT(16, 64);

        case Iop_32Sto64:return Iop_SEXT(32, 64);
        case Iop_32Uto64:return Iop_ZEXT(32, 64);
        case Iop_32UtoV128:return Iop_ZEXT(32, 128);
        case Iop_64UtoV128:return Iop_ZEXT(64, 128);

        case Iop_32to8:return Vns(m_ctx, Z3_mk_extract(m_ctx, 7, 0, a), 8);
        case Iop_64to8:return Vns(m_ctx, Z3_mk_extract(m_ctx, 7, 0, a), 8);
        case Iop_64to16:return Vns(m_ctx, Z3_mk_extract(m_ctx, 15, 0, a), 16);
        case Iop_32to16:return Vns(m_ctx, Z3_mk_extract(m_ctx, 15, 0, a), 16);
        case Iop_64to32:return Vns(m_ctx, Z3_mk_extract(m_ctx, 31, 0, a), 32);
        case Iop_V128to32:return Vns(m_ctx, Z3_mk_extract(m_ctx, 31, 0, a), 32);
        case Iop_V128to64:return Vns(m_ctx, Z3_mk_extract(m_ctx, 63, 0, a), 64);
        case Iop_128to64:return Vns(m_ctx, Z3_mk_extract(m_ctx, 63, 0, a), 64);
        case Iop_16HIto8:return Vns(m_ctx, Z3_mk_extract(m_ctx, 15, 8, a), 8);
        case Iop_32HIto16:return Vns(m_ctx, Z3_mk_extract(m_ctx, 31, 16, a), 16);
        case Iop_64HIto32:return Vns(m_ctx, Z3_mk_extract(m_ctx, 63, 32, a), 32);
        case Iop_V128HIto64:return Vns(m_ctx, Z3_mk_extract(m_ctx, 127, 64, a), 64);
        case Iop_128HIto64:return Vns(m_ctx, Z3_mk_extract(m_ctx, 127, 64, a), 64);

        case Iop_GetMSBs8x16: {
            Vns re(m_ctx, 0, 0);
            for (UInt i = 7; i < 16 * 8; i += 8) {
                re = a.extract(i, i).Concat(re);
            }
            return re;
        }

        case Iop_Clz32:vassert(a.bitn == 32); return 31 - bsr32(a);
        case Iop_Clz64:vassert(a.bitn == 64); return (ULong)63 - bsr64(a);
        case Iop_Ctz32:vassert(a.bitn == 32); return bsf32(a);//ok
        case Iop_Ctz64:vassert(a.bitn == 64); return bsf64(a);//ok
        };
    }else {
        switch (op) {
        case Iop_1Uto8:vassert(a.bitn == 1); return Vns(a, (UChar)((UChar)a ? 1 : 0));
        case Iop_1Uto32:vassert(a.bitn == 1); return Vns(a, (UInt)((UChar)a ? 1 : 0));
        case Iop_1Uto64:vassert(a.bitn == 1); return Vns(a, (ULong)((UChar)a ? 1 : 0));
        case Iop_1Sto8:vassert(a.bitn == 1); return Vns(a, (Char)((UChar)a ? -1 : 0));
        case Iop_1Sto16:vassert(a.bitn == 1); return Vns(a, (Short)((UChar)a ? -1 : 0));
        case Iop_1Sto32:vassert(a.bitn == 1); return Vns(a, (Int)((UChar)a ? -1 : 0));
        case Iop_1Sto64:vassert(a.bitn == 1); return Vns(a, (Long)((UChar)a ? -1 : 0));


        case Iop_32to1:vassert(a.bitn == 32); return Vns(a, ((UChar)a ? 1 : 0), 1);
        case Iop_64to1:vassert(a.bitn == 64); return Vns(a, ((UChar)a ? 1 : 0), 1);

        case Iop_Not1:return Vns(a, ((UChar)a & 0b1 ? 0 : 1), 1);
        case Iop_Not8:return Vns(a, (UChar)(~(UChar)a));
        case Iop_Not16:return Vns(a, (UShort)(~(UShort)a));
        case Iop_Not32:return Vns(a, (UInt)(~(UInt)a));
        case Iop_Not64:return Vns(a, (ULong)(~(ULong)a));
        case Iop_NotV256:return Vns(a, _mm256_not_si256(a));
        case Iop_NotV128:return Vns(a, _mm_not_si128(a));

        case Iop_8Sto16:return Iop_to(Char, Short);
        case Iop_8Sto32:return Iop_to(Char, Int);
        case Iop_8Sto64:return Iop_to(Char, Long);
        case Iop_8Uto16:return Iop_to(UChar, UShort);
        case Iop_8Uto32:return Iop_to(UChar, UInt);
        case Iop_8Uto64:return Iop_to(UChar, ULong);

        case Iop_16Sto32:return Iop_to(Short, Int);
        case Iop_16Sto64:return Iop_to(Short, Long);
        case Iop_16Uto32:return Iop_to(UShort, UInt);
        case Iop_16Uto64:return Iop_to(UShort, ULong);

        case Iop_32Sto64:return Iop_to(Int, Long);
        case Iop_32Uto64:return Iop_to(UInt, ULong);
        case Iop_32UtoV128:return Vns(a, _mm_set_epi32(0, 0, 0, a));
        case Iop_64UtoV128:return Vns(a, _mm_set_epi64x(0, a));

        case Iop_64to32:return Iop_to(ULong, UInt);
        case Iop_64to16:return Iop_to(ULong, UShort);
        case Iop_64to8 :return Iop_to(ULong, UChar);
        case Iop_64HIto32:return Vns(a, a.get<Int, 4>());
        case Iop_32to16:return Iop_to(UInt, UShort);
        case Iop_32to8:return Iop_to(UInt, UChar);
        case Iop_32HIto16:return Vns(a, a.get<UShort, 2>());


        case Iop_V128to32:return Vns(a, ((__m128i)a).m128i_u32[0]);//OK
        case Iop_V128to64:return Vns(a, ((__m128i)a).m128i_u64[0]);//OK
        case Iop_128to64:return Vns(a, ((__m128i)a).m128i_u64[0]);//OK
        case Iop_V128HIto64:return Vns(a, ((__m128i)a).m128i_u64[1]);//OK
        case Iop_V256toV128_0:return Vns(a, GET16(((__m256i)a).m256i_u64));
        case Iop_V256toV128_1:return Vns(a, GET16(((__m256i)a).m256i_u64+2));
        case Iop_128HIto64:return Vns(a, ((__m128i)a).m128i_u64[1]);//OK
        case Iop_16HIto8:return Vns(a, a.get<UChar,1>());//OK
        case Iop_GetMSBs8x16: return Vns(a, (UShort)_mm_movemask_epi8(a));//OK pmovmskb
        case Iop_Clz32:vassert(a.bitn == 32); return Vns(a, (UInt)CountLeadingZeros32(a));
        case Iop_Clz64:vassert(a.bitn == 64); return Vns(a, (ULong)CountLeadingZeros64(a));
        case Iop_Ctz32: {
            vassert(a.bitn == 32);
            unsigned long result = 0;
            if (!_BitScanForward(&result, (UInt)a)) {
                result = 32;
            }
            return Vns(a, (UInt)result);
        };//ok
        case Iop_Ctz64: {
            vassert(a.bitn == 64);
            unsigned long result = 0;
            if (!_BitScanForward64(&result, (ULong)a)) {
                result = 64;
            }
            return Vns(a, (ULong)result);
        };//ok bsf
        case Iop_Abs64Fx2:
        case Iop_Neg64Fx2:
        case Iop_RSqrtEst64Fx2:
        case Iop_RecipEst64Fx2:

        case Iop_Sqrt64F0x2:

        case Iop_Sqrt32Fx8:
        case Iop_RSqrtEst32Fx8:
        case Iop_RecipEst32Fx8:

        case Iop_Sqrt64Fx4:

        case Iop_RecipEst32Fx4:
        case Iop_RoundF32x4_RM:
        case Iop_RoundF32x4_RP:
        case Iop_RoundF32x4_RN:
        case Iop_RoundF32x4_RZ:
        case Iop_RecipEst32Ux4:
        case Iop_Abs32Fx4:
        case Iop_Neg32Fx4:
        case Iop_RSqrtEst32Fx4:

        case Iop_RecipEst32Fx2:
        case Iop_RecipEst32Ux2:
        case Iop_Abs32Fx2:
        case Iop_Neg32Fx2:
        case Iop_RSqrtEst32Fx2:

        case Iop_Sqrt32F0x4:
        case Iop_RSqrtEst32F0x4:
        case Iop_RecipEst32F0x4:

        case Iop_Dup8x16:
        case Iop_Dup16x8:
        case Iop_Dup32x4:
        case Iop_Reverse1sIn8_x16:
        case Iop_Reverse8sIn16_x8:
        case Iop_Reverse8sIn32_x4:
        case Iop_Reverse16sIn32_x4:
        case Iop_Reverse8sIn64_x2:
        case Iop_Reverse16sIn64_x2:
        case Iop_Reverse32sIn64_x2:

        case Iop_ZeroHI64ofV128:
        case Iop_ZeroHI96ofV128:
        case Iop_ZeroHI112ofV128:
        case Iop_ZeroHI120ofV128:

        case Iop_F128HItoF64:  /* F128 -> high half of F128 */
        case Iop_D128HItoD64:  /* D128 -> high half of D128 */
        case Iop_F128LOtoF64:  /* F128 -> low  half of F128 */
        case Iop_D128LOtoD64:  /* D128 -> low  half of D128 */

        case Iop_NegF128:
        case Iop_AbsF128:

        case Iop_I32StoF128: /* signed I32 -> F128 */
        case Iop_I64StoF128: /* signed I64 -> F128 */
        case Iop_I32UtoF128: /* unsigned I32 -> F128 */
        case Iop_I64UtoF128: /* unsigned I64 -> F128 */
        case Iop_F32toF128:  /* F32 -> F128 */
        case Iop_F64toF128:  /* F64 -> F128 */
        case Iop_I32StoD128: /* signed I64 -> D128 */
        case Iop_I64StoD128: /* signed I64 -> D128 */
        case Iop_I32UtoD128: /* unsigned I32 -> D128 */
        case Iop_I64UtoD128: /* unsigned I64 -> D128 */

        case Iop_F16toF64:goto FAILD;
        case Iop_F32toF64:return Vns(a, (double)((float)a));
        case Iop_I32StoF64:return Vns(a, (double)((Int)a));
        case Iop_I32UtoF64:return Vns(a, (double)((UInt)a));
        case Iop_NegF64:
        case Iop_AbsF64:
        case Iop_RSqrtEst5GoodF64:
        case Iop_RoundF64toF64_NEAREST:
        case Iop_RoundF64toF64_NegINF:
        case Iop_RoundF64toF64_PosINF:
        case Iop_RoundF64toF64_ZERO:
        case Iop_D32toD64:
        case Iop_I32StoD64:
        case Iop_I32UtoD64:
        case Iop_ExtractExpD64:    /* D64  -> I64 */
        case Iop_ExtractExpD128:   /* D128 -> I64 */
        case Iop_ExtractSigD64:    /* D64  -> I64 */
        case Iop_ExtractSigD128:   /* D128 -> I64 */
        case Iop_DPBtoBCD:
        case Iop_BCDtoDPB:

        case Iop_D64toD128:

        case Iop_TruncF64asF32:
        case Iop_NegF32:
        case Iop_AbsF32:
        case Iop_F16toF32:

        case Iop_Dup8x8:
        case Iop_Dup16x4:
        case Iop_Dup32x2:
        case Iop_Reverse8sIn16_x4:
        case Iop_Reverse8sIn32_x2:
        case Iop_Reverse16sIn32_x2:
        case Iop_Reverse8sIn64_x1:
        case Iop_Reverse16sIn64_x1:
        case Iop_Reverse32sIn64_x1:
        case Iop_V256to64_0: case Iop_V256to64_1:
        case Iop_V256to64_2: case Iop_V256to64_3:

        case Iop_GetMSBs8x8:


        case Iop_ReinterpF64asI64:
        case Iop_ReinterpI64asF64:
        case Iop_ReinterpI32asF32:
        case Iop_ReinterpF32asI32:
        case Iop_ReinterpI64asD64:
        case Iop_ReinterpD64asI64:

        case Iop_CmpNEZ8x8:
        case Iop_Cnt8x8:
        case Iop_Clz8x8:
        case Iop_Cls8x8:
        case Iop_Abs8x8:

        case Iop_CmpNEZ8x16:
        case Iop_Cnt8x16:
        case Iop_Clz8x16:
        case Iop_Cls8x16:
        case Iop_Abs8x16:

        case Iop_CmpNEZ16x4:
        case Iop_Clz16x4:
        case Iop_Cls16x4:
        case Iop_Abs16x4:

        case Iop_CmpNEZ16x8:
        case Iop_Clz16x8:
        case Iop_Cls16x8:
        case Iop_Abs16x8:

        case Iop_CmpNEZ32x2:
        case Iop_Clz32x2:
        case Iop_Cls32x2:
        case Iop_Abs32x2:

        case Iop_CmpNEZ32x4:
        case Iop_Clz32x4:
        case Iop_Cls32x4:
        case Iop_Abs32x4:
        case Iop_RSqrtEst32Ux4:

        case Iop_CmpwNEZ32:

        case Iop_CmpwNEZ64:

        case Iop_CmpNEZ64x2:
        case Iop_CipherSV128:
        case Iop_Clz64x2:
        case Iop_Abs64x2:

        case Iop_PwBitMtxXpose64x2:

        case Iop_NarrowUn16to8x8:
        case Iop_NarrowUn32to16x4:
        case Iop_NarrowUn64to32x2:
        case Iop_QNarrowUn16Sto8Sx8:
        case Iop_QNarrowUn16Sto8Ux8:
        case Iop_QNarrowUn16Uto8Ux8:
        case Iop_QNarrowUn32Sto16Sx4:
        case Iop_QNarrowUn32Sto16Ux4:
        case Iop_QNarrowUn32Uto16Ux4:
        case Iop_QNarrowUn64Sto32Sx2:
        case Iop_QNarrowUn64Sto32Ux2:
        case Iop_QNarrowUn64Uto32Ux2:

        case Iop_Widen8Sto16x8:
        case Iop_Widen8Uto16x8:
        case Iop_Widen16Sto32x4:
        case Iop_Widen16Uto32x4:
        case Iop_Widen32Sto64x2:
        case Iop_Widen32Uto64x2:

        case Iop_PwAddL32Ux2:
        case Iop_PwAddL32Sx2:

        case Iop_PwAddL16Ux4:
        case Iop_PwAddL16Sx4:

        case Iop_PwAddL8Ux8:
        case Iop_PwAddL8Sx8:

        case Iop_PwAddL32Ux4:
        case Iop_PwAddL32Sx4:

        case Iop_PwAddL16Ux8:
        case Iop_PwAddL16Sx8:

        case Iop_PwAddL8Ux16:
        case Iop_PwAddL8Sx16:

        case Iop_I64UtoF32:
        default:
            goto FAILD;
        }
    }
FAILD:
    vex_printf("unsupport Unop: ");
    ppIROp(op);
    vpanic("tIRType");
}

#undef Iop_ZEXT
#undef Iop_SEXT
#undef Iop_to
