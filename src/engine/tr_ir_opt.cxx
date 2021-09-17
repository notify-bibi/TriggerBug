
#include "instopt/engine/tr_ir_opt.h"



ppIR::~ppIR()
{
    if (m_logger) {
        m_logger->log(m_leve, m_str);
    }
}
;

UInt ppIR::vex_printf(const HChar* format, ...)

{
    HChar myprintf_buf[1000];

    UInt ret;
    va_list vargs;
    va_start(vargs, format);
    ret = vsnprintf_s(myprintf_buf, sizeof(myprintf_buf), _TRUNCATE, format, vargs);
    va_end(vargs);
    m_str.append(myprintf_buf);
    return ret;
}

 void ppIR::ppIRType(IRType ty)
{
    switch (ty) {
    case Ity_INVALID: vex_printf("Ity_INVALID"); break;
    case Ity_I1:      vex_printf("I1");   break;
    case Ity_I8:      vex_printf("I8");   break;
    case Ity_I16:     vex_printf("I16");  break;
    case Ity_I32:     vex_printf("I32");  break;
    case Ity_I64:     vex_printf("I64");  break;
    case Ity_I128:    vex_printf("I128"); break;
    case Ity_F16:     vex_printf("F16");  break;
    case Ity_F32:     vex_printf("F32");  break;
    case Ity_F64:     vex_printf("F64");  break;
    case Ity_F128:    vex_printf("F128"); break;
    case Ity_D32:     vex_printf("D32");  break;
    case Ity_D64:     vex_printf("D64");  break;
    case Ity_D128:    vex_printf("D128"); break;
    case Ity_V128:    vex_printf("V128"); break;
    case Ity_V256:    vex_printf("V256"); break;
    default: vex_printf("ty = 0x%x\n", (UInt)ty);
        VPANIC("ppIRType");
    }
}

 void ppIR::ppIRConst(const IRConst* con)
{
    union { ULong i64; Double f64; UInt i32; Float f32; } u;
    vassert(sizeof(ULong) == sizeof(Double));
    switch (con->tag) {
    case Ico_U1:   vex_printf("%d:I1", con->Ico.U1 ? 1 : 0); break;
    case Ico_U8:   vex_printf("0x%x:I8", (UInt)(con->Ico.U8)); break;
    case Ico_U16:  vex_printf("0x%x:I16", (UInt)(con->Ico.U16)); break;
    case Ico_U32:  vex_printf("0x%x:I32", (UInt)(con->Ico.U32)); break;
    case Ico_U64:  vex_printf("0x%llx:I64", (ULong)(con->Ico.U64)); break;
    case Ico_F32:  u.f32 = con->Ico.F32;
        vex_printf("F32{0x%x}", u.i32);
        break;
    case Ico_F32i: vex_printf("F32i{0x%x}", con->Ico.F32i); break;
    case Ico_F64:  u.f64 = con->Ico.F64;
        vex_printf("F64{0x%llx}", u.i64);
        break;
    case Ico_F64i: vex_printf("F64i{0x%llx}", con->Ico.F64i); break;
    case Ico_V128: vex_printf("V128{0x%04x}", (UInt)(con->Ico.V128)); break;
    case Ico_V256: vex_printf("V256{0x%08x}", con->Ico.V256); break;
    default: VPANIC("ppIRConst");
    }
}

 void ppIR::ppIRCallee(const IRCallee* ce)
{
    vex_printf("%s", ce->name);
    if (ce->regparms > 0)
        vex_printf("[rp=%d]", ce->regparms);
    if (ce->mcx_mask > 0)
        vex_printf("[mcx=0x%x]", ce->mcx_mask);
    vex_printf("{%p}", (void*)ce->addr);
}

 void ppIR::ppIRRegArray(const IRRegArray* arr)
{
    vex_printf("(%d:%dx", arr->base, arr->nElems);
    ppIRType(arr->elemTy);
    vex_printf(")");
}

 void ppIR::ppIRTemp(IRTemp tmp)
{
    if (tmp == IRTemp_INVALID)
        vex_printf("IRTemp_INVALID");
    else
        vex_printf("t%u", tmp);
}

 void ppIR::ppIROp(IROp op)
{
    const HChar* str = NULL;
    IROp   base;
    switch (op) {
    case Iop_Add8 ... Iop_Add64:
        str = "Add"; base = Iop_Add8; break;
    case Iop_Sub8 ... Iop_Sub64:
        str = "Sub"; base = Iop_Sub8; break;
    case Iop_Mul8 ... Iop_Mul64:
        str = "Mul"; base = Iop_Mul8; break;
    case Iop_Or8 ... Iop_Or64:
        str = "Or"; base = Iop_Or8; break;
    case Iop_And8 ... Iop_And64:
        str = "And"; base = Iop_And8; break;
    case Iop_Xor8 ... Iop_Xor64:
        str = "Xor"; base = Iop_Xor8; break;
    case Iop_Shl8 ... Iop_Shl64:
        str = "Shl"; base = Iop_Shl8; break;
    case Iop_Shr8 ... Iop_Shr64:
        str = "Shr"; base = Iop_Shr8; break;
    case Iop_Sar8 ... Iop_Sar64:
        str = "Sar"; base = Iop_Sar8; break;
    case Iop_CmpEQ8 ... Iop_CmpEQ64:
        str = "CmpEQ"; base = Iop_CmpEQ8; break;
    case Iop_CmpNE8 ... Iop_CmpNE64:
        str = "CmpNE"; base = Iop_CmpNE8; break;
    case Iop_CasCmpEQ8 ... Iop_CasCmpEQ64:
        str = "CasCmpEQ"; base = Iop_CasCmpEQ8; break;
    case Iop_CasCmpNE8 ... Iop_CasCmpNE64:
        str = "CasCmpNE"; base = Iop_CasCmpNE8; break;
    case Iop_ExpCmpNE8 ... Iop_ExpCmpNE64:
        str = "ExpCmpNE"; base = Iop_ExpCmpNE8; break;
    case Iop_Not8 ... Iop_Not64:
        str = "Not"; base = Iop_Not8; break;
        /* other cases must explicitly "return;" */
    case Iop_8Uto16:   vex_printf("8Uto16");  return;
    case Iop_8Uto32:   vex_printf("8Uto32");  return;
    case Iop_16Uto32:  vex_printf("16Uto32"); return;
    case Iop_8Sto16:   vex_printf("8Sto16");  return;
    case Iop_8Sto32:   vex_printf("8Sto32");  return;
    case Iop_16Sto32:  vex_printf("16Sto32"); return;
    case Iop_32Sto64:  vex_printf("32Sto64"); return;
    case Iop_32Uto64:  vex_printf("32Uto64"); return;
    case Iop_32to8:    vex_printf("32to8");   return;
    case Iop_16Uto64:  vex_printf("16Uto64"); return;
    case Iop_16Sto64:  vex_printf("16Sto64"); return;
    case Iop_8Uto64:   vex_printf("8Uto64"); return;
    case Iop_8Sto64:   vex_printf("8Sto64"); return;
    case Iop_64to16:   vex_printf("64to16"); return;
    case Iop_64to8:    vex_printf("64to8");  return;

    case Iop_Not1:     vex_printf("Not1");    return;
    case Iop_And1:     vex_printf("And1");    return;
    case Iop_Or1:      vex_printf("Or1");     return;
    case Iop_32to1:    vex_printf("32to1");   return;
    case Iop_64to1:    vex_printf("64to1");   return;
    case Iop_1Uto8:    vex_printf("1Uto8");   return;
    case Iop_1Uto32:   vex_printf("1Uto32");  return;
    case Iop_1Uto64:   vex_printf("1Uto64");  return;
    case Iop_1Sto8:    vex_printf("1Sto8");  return;
    case Iop_1Sto16:   vex_printf("1Sto16");  return;
    case Iop_1Sto32:   vex_printf("1Sto32");  return;
    case Iop_1Sto64:   vex_printf("1Sto64");  return;

    case Iop_MullS8:   vex_printf("MullS8");  return;
    case Iop_MullS16:  vex_printf("MullS16"); return;
    case Iop_MullS32:  vex_printf("MullS32"); return;
    case Iop_MullS64:  vex_printf("MullS64"); return;
    case Iop_MullU8:   vex_printf("MullU8");  return;
    case Iop_MullU16:  vex_printf("MullU16"); return;
    case Iop_MullU32:  vex_printf("MullU32"); return;
    case Iop_MullU64:  vex_printf("MullU64"); return;

    case Iop_Clz64:    vex_printf("Clz64"); return;
    case Iop_Clz32:    vex_printf("Clz32"); return;
    case Iop_Ctz64:    vex_printf("Ctz64"); return;
    case Iop_Ctz32:    vex_printf("Ctz32"); return;

    case Iop_ClzNat64: vex_printf("ClzNat64"); return;
    case Iop_ClzNat32: vex_printf("ClzNat32"); return;
    case Iop_CtzNat64: vex_printf("CtzNat64"); return;
    case Iop_CtzNat32: vex_printf("CtzNat32"); return;

    case Iop_PopCount64: vex_printf("PopCount64"); return;
    case Iop_PopCount32: vex_printf("PopCount32"); return;

    case Iop_CmpLT32S: vex_printf("CmpLT32S"); return;
    case Iop_CmpLE32S: vex_printf("CmpLE32S"); return;
    case Iop_CmpLT32U: vex_printf("CmpLT32U"); return;
    case Iop_CmpLE32U: vex_printf("CmpLE32U"); return;

    case Iop_CmpLT64S: vex_printf("CmpLT64S"); return;
    case Iop_CmpLE64S: vex_printf("CmpLE64S"); return;
    case Iop_CmpLT64U: vex_printf("CmpLT64U"); return;
    case Iop_CmpLE64U: vex_printf("CmpLE64U"); return;

    case Iop_CmpNEZ8:  vex_printf("CmpNEZ8"); return;
    case Iop_CmpNEZ16: vex_printf("CmpNEZ16"); return;
    case Iop_CmpNEZ32: vex_printf("CmpNEZ32"); return;
    case Iop_CmpNEZ64: vex_printf("CmpNEZ64"); return;

    case Iop_CmpwNEZ32: vex_printf("CmpwNEZ32"); return;
    case Iop_CmpwNEZ64: vex_printf("CmpwNEZ64"); return;

    case Iop_Left8:  vex_printf("Left8"); return;
    case Iop_Left16: vex_printf("Left16"); return;
    case Iop_Left32: vex_printf("Left32"); return;
    case Iop_Left64: vex_printf("Left64"); return;
    case Iop_Max32U: vex_printf("Max32U"); return;

    case Iop_CmpORD32U: vex_printf("CmpORD32U"); return;
    case Iop_CmpORD32S: vex_printf("CmpORD32S"); return;

    case Iop_CmpORD64U: vex_printf("CmpORD64U"); return;
    case Iop_CmpORD64S: vex_printf("CmpORD64S"); return;

    case Iop_DivU32: vex_printf("DivU32"); return;
    case Iop_DivS32: vex_printf("DivS32"); return;
    case Iop_DivU64: vex_printf("DivU64"); return;
    case Iop_DivS64: vex_printf("DivS64"); return;
    case Iop_DivU64E: vex_printf("DivU64E"); return;
    case Iop_DivS64E: vex_printf("DivS64E"); return;
    case Iop_DivU32E: vex_printf("DivU32E"); return;
    case Iop_DivS32E: vex_printf("DivS32E"); return;

    case Iop_DivModU64to32: vex_printf("DivModU64to32"); return;
    case Iop_DivModS64to32: vex_printf("DivModS64to32"); return;

    case Iop_DivModU32to32: vex_printf("DivModU32to32"); return;
    case Iop_DivModS32to32: vex_printf("DivModS32to32"); return;

    case Iop_DivModU128to64: vex_printf("DivModU128to64"); return;
    case Iop_DivModS128to64: vex_printf("DivModS128to64"); return;

    case Iop_DivModS64to64: vex_printf("DivModS64to64"); return;
    case Iop_DivModU64to64: vex_printf("DivModU64to64"); return;

    case Iop_16HIto8:  vex_printf("16HIto8"); return;
    case Iop_16to8:    vex_printf("16to8");   return;
    case Iop_8HLto16:  vex_printf("8HLto16"); return;

    case Iop_32HIto16: vex_printf("32HIto16"); return;
    case Iop_32to16:   vex_printf("32to16");   return;
    case Iop_16HLto32: vex_printf("16HLto32"); return;

    case Iop_64HIto32: vex_printf("64HIto32"); return;
    case Iop_64to32:   vex_printf("64to32");   return;
    case Iop_32HLto64: vex_printf("32HLto64"); return;

    case Iop_128HIto64: vex_printf("128HIto64"); return;
    case Iop_128to64:   vex_printf("128to64");   return;
    case Iop_64HLto128: vex_printf("64HLto128"); return;

    case Iop_CmpF32:    vex_printf("CmpF32");    return;
    case Iop_F32toI32S: vex_printf("F32toI32S");  return;
    case Iop_F32toI64S: vex_printf("F32toI64S");  return;
    case Iop_I32StoF32: vex_printf("I32StoF32");  return;
    case Iop_I64StoF32: vex_printf("I64StoF32");  return;

    case Iop_AddF64:    vex_printf("AddF64"); return;
    case Iop_SubF64:    vex_printf("SubF64"); return;
    case Iop_MulF64:    vex_printf("MulF64"); return;
    case Iop_DivF64:    vex_printf("DivF64"); return;
    case Iop_AddF64r32: vex_printf("AddF64r32"); return;
    case Iop_SubF64r32: vex_printf("SubF64r32"); return;
    case Iop_MulF64r32: vex_printf("MulF64r32"); return;
    case Iop_DivF64r32: vex_printf("DivF64r32"); return;
    case Iop_AddF32:    vex_printf("AddF32"); return;
    case Iop_SubF32:    vex_printf("SubF32"); return;
    case Iop_MulF32:    vex_printf("MulF32"); return;
    case Iop_DivF32:    vex_printf("DivF32"); return;

        /* 128 bit floating point */
    case Iop_AddF128:   vex_printf("AddF128");  return;
    case Iop_SubF128:   vex_printf("SubF128");  return;
    case Iop_MulF128:   vex_printf("MulF128");  return;
    case Iop_DivF128:   vex_printf("DivF128");  return;

    case Iop_TruncF128toI64S:   vex_printf("TruncF128toI64S");  return;
    case Iop_TruncF128toI32S:   vex_printf("TruncF128toI32S");  return;
    case Iop_TruncF128toI64U:   vex_printf("TruncF128toI64U");  return;
    case Iop_TruncF128toI32U:   vex_printf("TruncF128toI32U");  return;

    case Iop_MAddF128:   vex_printf("MAddF128");  return;
    case Iop_MSubF128:   vex_printf("MSubF128");  return;
    case Iop_NegMAddF128:   vex_printf("NegMAddF128");  return;
    case Iop_NegMSubF128:   vex_printf("NegMSubF128");  return;

    case Iop_AbsF128:   vex_printf("AbsF128");  return;
    case Iop_NegF128:   vex_printf("NegF128");  return;
    case Iop_SqrtF128:  vex_printf("SqrtF128"); return;
    case Iop_CmpF128:   vex_printf("CmpF128");  return;

    case Iop_F64HLtoF128: vex_printf("F64HLtoF128"); return;
    case Iop_F128HItoF64: vex_printf("F128HItoF64"); return;
    case Iop_F128LOtoF64: vex_printf("F128LOtoF64"); return;
    case Iop_I32StoF128: vex_printf("I32StoF128"); return;
    case Iop_I64StoF128: vex_printf("I64StoF128"); return;
    case Iop_I32UtoF128: vex_printf("I32UtoF128"); return;
    case Iop_I64UtoF128: vex_printf("I64UtoF128"); return;
    case Iop_F128toI32S: vex_printf("F128toI32S"); return;
    case Iop_F128toI64S: vex_printf("F128toI64S"); return;
    case Iop_F128toI32U: vex_printf("F128toI32U"); return;
    case Iop_F128toI64U: vex_printf("F128toI64U"); return;
    case Iop_F32toF128:  vex_printf("F32toF128");  return;
    case Iop_F64toF128:  vex_printf("F64toF128");  return;
    case Iop_F128toF64:  vex_printf("F128toF64");  return;
    case Iop_F128toF32:  vex_printf("F128toF32");  return;
    case Iop_F128toI128S: vex_printf("F128toI128");  return;
    case Iop_RndF128:    vex_printf("RndF128");  return;

        /* s390 specific */
    case Iop_MAddF32:    vex_printf("s390_MAddF32"); return;
    case Iop_MSubF32:    vex_printf("s390_MSubF32"); return;

    case Iop_ScaleF64:      vex_printf("ScaleF64"); return;
    case Iop_AtanF64:       vex_printf("AtanF64"); return;
    case Iop_Yl2xF64:       vex_printf("Yl2xF64"); return;
    case Iop_Yl2xp1F64:     vex_printf("Yl2xp1F64"); return;
    case Iop_PRemF64:       vex_printf("PRemF64"); return;
    case Iop_PRemC3210F64:  vex_printf("PRemC3210F64"); return;
    case Iop_PRem1F64:      vex_printf("PRem1F64"); return;
    case Iop_PRem1C3210F64: vex_printf("PRem1C3210F64"); return;
    case Iop_NegF64:        vex_printf("NegF64"); return;
    case Iop_AbsF64:        vex_printf("AbsF64"); return;
    case Iop_NegF32:        vex_printf("NegF32"); return;
    case Iop_AbsF32:        vex_printf("AbsF32"); return;
    case Iop_SqrtF64:       vex_printf("SqrtF64"); return;
    case Iop_SqrtF32:       vex_printf("SqrtF32"); return;
    case Iop_SinF64:    vex_printf("SinF64"); return;
    case Iop_CosF64:    vex_printf("CosF64"); return;
    case Iop_TanF64:    vex_printf("TanF64"); return;
    case Iop_2xm1F64:   vex_printf("2xm1F64"); return;

    case Iop_MAddF64:    vex_printf("MAddF64"); return;
    case Iop_MSubF64:    vex_printf("MSubF64"); return;
    case Iop_MAddF64r32: vex_printf("MAddF64r32"); return;
    case Iop_MSubF64r32: vex_printf("MSubF64r32"); return;

    case Iop_RSqrtEst5GoodF64: vex_printf("RSqrtEst5GoodF64"); return;
    case Iop_RoundF64toF64_NEAREST: vex_printf("RoundF64toF64_NEAREST"); return;
    case Iop_RoundF64toF64_NegINF: vex_printf("RoundF64toF64_NegINF"); return;
    case Iop_RoundF64toF64_PosINF: vex_printf("RoundF64toF64_PosINF"); return;
    case Iop_RoundF64toF64_ZERO: vex_printf("RoundF64toF64_ZERO"); return;

    case Iop_TruncF64asF32: vex_printf("TruncF64asF32"); return;

    case Iop_RecpExpF64: vex_printf("RecpExpF64"); return;
    case Iop_RecpExpF32: vex_printf("RecpExpF32"); return;

    case Iop_MaxNumF64: vex_printf("MaxNumF64"); return;
    case Iop_MinNumF64: vex_printf("MinNumF64"); return;
    case Iop_MaxNumF32: vex_printf("MaxNumF32"); return;
    case Iop_MinNumF32: vex_printf("MinNumF32"); return;

    case Iop_F16toF64: vex_printf("F16toF64"); return;
    case Iop_F64toF16: vex_printf("F64toF16"); return;
    case Iop_F16toF32: vex_printf("F16toF32"); return;
    case Iop_F32toF16: vex_printf("F32toF16"); return;

    case Iop_QAdd32S: vex_printf("QAdd32S"); return;
    case Iop_QSub32S: vex_printf("QSub32S"); return;
    case Iop_Add16x2:   vex_printf("Add16x2"); return;
    case Iop_Sub16x2:   vex_printf("Sub16x2"); return;
    case Iop_QAdd16Sx2: vex_printf("QAdd16Sx2"); return;
    case Iop_QAdd16Ux2: vex_printf("QAdd16Ux2"); return;
    case Iop_QSub16Sx2: vex_printf("QSub16Sx2"); return;
    case Iop_QSub16Ux2: vex_printf("QSub16Ux2"); return;
    case Iop_HAdd16Ux2: vex_printf("HAdd16Ux2"); return;
    case Iop_HAdd16Sx2: vex_printf("HAdd16Sx2"); return;
    case Iop_HSub16Ux2: vex_printf("HSub16Ux2"); return;
    case Iop_HSub16Sx2: vex_printf("HSub16Sx2"); return;

    case Iop_Add8x4:   vex_printf("Add8x4"); return;
    case Iop_Sub8x4:   vex_printf("Sub8x4"); return;
    case Iop_QAdd8Sx4: vex_printf("QAdd8Sx4"); return;
    case Iop_QAdd8Ux4: vex_printf("QAdd8Ux4"); return;
    case Iop_QSub8Sx4: vex_printf("QSub8Sx4"); return;
    case Iop_QSub8Ux4: vex_printf("QSub8Ux4"); return;
    case Iop_HAdd8Ux4: vex_printf("HAdd8Ux4"); return;
    case Iop_HAdd8Sx4: vex_printf("HAdd8Sx4"); return;
    case Iop_HSub8Ux4: vex_printf("HSub8Ux4"); return;
    case Iop_HSub8Sx4: vex_printf("HSub8Sx4"); return;
    case Iop_Sad8Ux4:  vex_printf("Sad8Ux4"); return;

    case Iop_CmpNEZ16x2: vex_printf("CmpNEZ16x2"); return;
    case Iop_CmpNEZ8x4:  vex_printf("CmpNEZ8x4"); return;
    case Iop_Reverse8sIn32_x1: vex_printf("Reverse8sIn32_x1"); return;

    case Iop_CmpF64:    vex_printf("CmpF64"); return;

    case Iop_F64toI16S: vex_printf("F64toI16S"); return;
    case Iop_F64toI32S: vex_printf("F64toI32S"); return;
    case Iop_F64toI64S: vex_printf("F64toI64S"); return;
    case Iop_F64toI64U: vex_printf("F64toI64U"); return;
    case Iop_F32toI32U: vex_printf("F32toI32U");  return;
    case Iop_F32toI64U: vex_printf("F32toI64U");  return;

    case Iop_F64toI32U: vex_printf("F64toI32U"); return;

    case Iop_I32StoF64: vex_printf("I32StoF64"); return;
    case Iop_I64StoF64: vex_printf("I64StoF64"); return;
    case Iop_I64UtoF64: vex_printf("I64UtoF64"); return;
    case Iop_I32UtoF32: vex_printf("I32UtoF32"); return;
    case Iop_I64UtoF32: vex_printf("I64UtoF32"); return;

    case Iop_I32UtoF64: vex_printf("I32UtoF64"); return;

    case Iop_F32toF64: vex_printf("F32toF64"); return;
    case Iop_F64toF32: vex_printf("F64toF32"); return;

    case Iop_RoundF128toInt: vex_printf("RoundF128toInt"); return;
    case Iop_RoundF64toInt: vex_printf("RoundF64toInt"); return;
    case Iop_RoundF32toInt: vex_printf("RoundF32toInt"); return;
    case Iop_RoundF64toF32: vex_printf("RoundF64toF32"); return;

    case Iop_ReinterpF64asI64: vex_printf("ReinterpF64asI64"); return;
    case Iop_ReinterpI64asF64: vex_printf("ReinterpI64asF64"); return;
    case Iop_ReinterpF32asI32: vex_printf("ReinterpF32asI32"); return;
    case Iop_ReinterpI32asF32: vex_printf("ReinterpI32asF32"); return;

    case Iop_I32UtoF32x4_DEP: vex_printf("I32UtoF32x4_DEP"); return;
    case Iop_I32StoF32x4_DEP: vex_printf("I32StoF32x4_DEP"); return;

    case Iop_I32StoF32x4: vex_printf("I32StoF32x4"); return;
    case Iop_F32toI32Sx4: vex_printf("F32toI32Sx4"); return;

    case Iop_F32toF16x4_DEP: vex_printf("F32toF16x4_DEP"); return;
    case Iop_F32toF16x4: vex_printf("F32toF16x4"); return;
    case Iop_F16toF32x4: vex_printf("F16toF32x4"); return;
    case Iop_F16toF64x2: vex_printf("F16toF64x2"); return;
    case Iop_F64toF16x2_DEP: vex_printf("F64toF16x2_DEP"); return;

    case Iop_RSqrtEst32Fx4: vex_printf("RSqrtEst32Fx4"); return;
    case Iop_RSqrtEst32Ux4: vex_printf("RSqrtEst32Ux4"); return;
    case Iop_RSqrtEst32Fx2: vex_printf("RSqrtEst32Fx2"); return;
    case Iop_RSqrtEst32Ux2: vex_printf("RSqrtEst32Ux2"); return;

    case Iop_QF32toI32Ux4_RZ: vex_printf("QF32toI32Ux4_RZ"); return;
    case Iop_QF32toI32Sx4_RZ: vex_printf("QF32toI32Sx4_RZ"); return;

    case Iop_F32toI32Ux4_RZ: vex_printf("F32toI32Ux4_RZ"); return;
    case Iop_F32toI32Sx4_RZ: vex_printf("F32toI32Sx4_RZ"); return;

    case Iop_I32UtoF32x2_DEP: vex_printf("I32UtoF32x2_DEP"); return;
    case Iop_I32StoF32x2_DEP: vex_printf("I32StoF32x2_DEP"); return;

    case Iop_F32toI32Ux2_RZ: vex_printf("F32toI32Ux2_RZ"); return;
    case Iop_F32toI32Sx2_RZ: vex_printf("F32toI32Sx2_RZ"); return;

    case Iop_RoundF32x4_RM: vex_printf("RoundF32x4_RM"); return;
    case Iop_RoundF32x4_RP: vex_printf("RoundF32x4_RP"); return;
    case Iop_RoundF32x4_RN: vex_printf("RoundF32x4_RN"); return;
    case Iop_RoundF32x4_RZ: vex_printf("RoundF32x4_RZ"); return;

    case Iop_Abs8x8: vex_printf("Abs8x8"); return;
    case Iop_Abs16x4: vex_printf("Abs16x4"); return;
    case Iop_Abs32x2: vex_printf("Abs32x2"); return;
    case Iop_Add8x8: vex_printf("Add8x8"); return;
    case Iop_Add16x4: vex_printf("Add16x4"); return;
    case Iop_Add32x2: vex_printf("Add32x2"); return;
    case Iop_QAdd8Ux8: vex_printf("QAdd8Ux8"); return;
    case Iop_QAdd16Ux4: vex_printf("QAdd16Ux4"); return;
    case Iop_QAdd32Ux2: vex_printf("QAdd32Ux2"); return;
    case Iop_QAdd64Ux1: vex_printf("QAdd64Ux1"); return;
    case Iop_QAdd8Sx8: vex_printf("QAdd8Sx8"); return;
    case Iop_QAdd16Sx4: vex_printf("QAdd16Sx4"); return;
    case Iop_QAdd32Sx2: vex_printf("QAdd32Sx2"); return;
    case Iop_QAdd64Sx1: vex_printf("QAdd64Sx1"); return;
    case Iop_PwAdd8x8: vex_printf("PwAdd8x8"); return;
    case Iop_PwAdd16x4: vex_printf("PwAdd16x4"); return;
    case Iop_PwAdd32x2: vex_printf("PwAdd32x2"); return;
    case Iop_PwAdd32Fx2: vex_printf("PwAdd32Fx2"); return;
    case Iop_PwAddL8Ux8: vex_printf("PwAddL8Ux8"); return;
    case Iop_PwAddL16Ux4: vex_printf("PwAddL16Ux4"); return;
    case Iop_PwAddL32Ux2: vex_printf("PwAddL32Ux2"); return;
    case Iop_PwAddL8Sx8: vex_printf("PwAddL8Sx8"); return;
    case Iop_PwAddL16Sx4: vex_printf("PwAddL16Sx4"); return;
    case Iop_PwAddL32Sx2: vex_printf("PwAddL32Sx2"); return;
    case Iop_Sub8x8: vex_printf("Sub8x8"); return;
    case Iop_Sub16x4: vex_printf("Sub16x4"); return;
    case Iop_Sub32x2: vex_printf("Sub32x2"); return;
    case Iop_QSub8Ux8: vex_printf("QSub8Ux8"); return;
    case Iop_QSub16Ux4: vex_printf("QSub16Ux4"); return;
    case Iop_QSub32Ux2: vex_printf("QSub32Ux2"); return;
    case Iop_QSub64Ux1: vex_printf("QSub64Ux1"); return;
    case Iop_QSub8Sx8: vex_printf("QSub8Sx8"); return;
    case Iop_QSub16Sx4: vex_printf("QSub16Sx4"); return;
    case Iop_QSub32Sx2: vex_printf("QSub32Sx2"); return;
    case Iop_QSub64Sx1: vex_printf("QSub64Sx1"); return;
    case Iop_Mul8x8: vex_printf("Mul8x8"); return;
    case Iop_Mul16x4: vex_printf("Mul16x4"); return;
    case Iop_Mul32x2: vex_printf("Mul32x2"); return;
    case Iop_Mul32Fx2: vex_printf("Mul32Fx2"); return;
    case Iop_PolynomialMul8x8: vex_printf("PolynomialMul8x8"); return;
    case Iop_MulHi16Ux4: vex_printf("MulHi16Ux4"); return;
    case Iop_MulHi16Sx4: vex_printf("MulHi16Sx4"); return;
    case Iop_QDMulHi16Sx4: vex_printf("QDMulHi16Sx4"); return;
    case Iop_QDMulHi32Sx2: vex_printf("QDMulHi32Sx2"); return;
    case Iop_QRDMulHi16Sx4: vex_printf("QRDMulHi16Sx4"); return;
    case Iop_QRDMulHi32Sx2: vex_printf("QRDMulHi32Sx2"); return;
    case Iop_QDMull16Sx4: vex_printf("QDMull16Sx4"); return;
    case Iop_QDMull32Sx2: vex_printf("QDMull32Sx2"); return;
    case Iop_Avg8Ux8: vex_printf("Avg8Ux8"); return;
    case Iop_Avg16Ux4: vex_printf("Avg16Ux4"); return;
    case Iop_Max8Sx8: vex_printf("Max8Sx8"); return;
    case Iop_Max16Sx4: vex_printf("Max16Sx4"); return;
    case Iop_Max32Sx2: vex_printf("Max32Sx2"); return;
    case Iop_Max8Ux8: vex_printf("Max8Ux8"); return;
    case Iop_Max16Ux4: vex_printf("Max16Ux4"); return;
    case Iop_Max32Ux2: vex_printf("Max32Ux2"); return;
    case Iop_Min8Sx8: vex_printf("Min8Sx8"); return;
    case Iop_Min16Sx4: vex_printf("Min16Sx4"); return;
    case Iop_Min32Sx2: vex_printf("Min32Sx2"); return;
    case Iop_Min8Ux8: vex_printf("Min8Ux8"); return;
    case Iop_Min16Ux4: vex_printf("Min16Ux4"); return;
    case Iop_Min32Ux2: vex_printf("Min32Ux2"); return;
    case Iop_PwMax8Sx8: vex_printf("PwMax8Sx8"); return;
    case Iop_PwMax16Sx4: vex_printf("PwMax16Sx4"); return;
    case Iop_PwMax32Sx2: vex_printf("PwMax32Sx2"); return;
    case Iop_PwMax8Ux8: vex_printf("PwMax8Ux8"); return;
    case Iop_PwMax16Ux4: vex_printf("PwMax16Ux4"); return;
    case Iop_PwMax32Ux2: vex_printf("PwMax32Ux2"); return;
    case Iop_PwMin8Sx8: vex_printf("PwMin8Sx8"); return;
    case Iop_PwMin16Sx4: vex_printf("PwMin16Sx4"); return;
    case Iop_PwMin32Sx2: vex_printf("PwMin32Sx2"); return;
    case Iop_PwMin8Ux8: vex_printf("PwMin8Ux8"); return;
    case Iop_PwMin16Ux4: vex_printf("PwMin16Ux4"); return;
    case Iop_PwMin32Ux2: vex_printf("PwMin32Ux2"); return;
    case Iop_CmpEQ8x8: vex_printf("CmpEQ8x8"); return;
    case Iop_CmpEQ16x4: vex_printf("CmpEQ16x4"); return;
    case Iop_CmpEQ32x2: vex_printf("CmpEQ32x2"); return;
    case Iop_CmpGT8Ux8: vex_printf("CmpGT8Ux8"); return;
    case Iop_CmpGT16Ux4: vex_printf("CmpGT16Ux4"); return;
    case Iop_CmpGT32Ux2: vex_printf("CmpGT32Ux2"); return;
    case Iop_CmpGT8Sx8: vex_printf("CmpGT8Sx8"); return;
    case Iop_CmpGT16Sx4: vex_printf("CmpGT16Sx4"); return;
    case Iop_CmpGT32Sx2: vex_printf("CmpGT32Sx2"); return;
    case Iop_Cnt8x8: vex_printf("Cnt8x8"); return;
    case Iop_Clz8x8: vex_printf("Clz8x8"); return;
    case Iop_Clz16x4: vex_printf("Clz16x4"); return;
    case Iop_Clz32x2: vex_printf("Clz32x2"); return;
    case Iop_Cls8x8: vex_printf("Cls8x8"); return;
    case Iop_Cls16x4: vex_printf("Cls16x4"); return;
    case Iop_Cls32x2: vex_printf("Cls32x2"); return;
    case Iop_ShlN8x8: vex_printf("ShlN8x8"); return;
    case Iop_ShlN16x4: vex_printf("ShlN16x4"); return;
    case Iop_ShlN32x2: vex_printf("ShlN32x2"); return;
    case Iop_ShrN8x8: vex_printf("ShrN8x8"); return;
    case Iop_ShrN16x4: vex_printf("ShrN16x4"); return;
    case Iop_ShrN32x2: vex_printf("ShrN32x2"); return;
    case Iop_SarN8x8: vex_printf("SarN8x8"); return;
    case Iop_SarN16x4: vex_printf("SarN16x4"); return;
    case Iop_SarN32x2: vex_printf("SarN32x2"); return;
    case Iop_QNarrowBin16Sto8Ux8: vex_printf("QNarrowBin16Sto8Ux8"); return;
    case Iop_QNarrowBin16Sto8Sx8: vex_printf("QNarrowBin16Sto8Sx8"); return;
    case Iop_QNarrowBin32Sto16Sx4: vex_printf("QNarrowBin32Sto16Sx4"); return;
    case Iop_QNarrowBin64Sto32Sx4: vex_printf("QNarrowBin64Sto32Sx4"); return;
    case Iop_QNarrowBin64Uto32Ux4: vex_printf("QNarrowBin64Uto32Ux4"); return;
    case Iop_NarrowBin16to8x8: vex_printf("NarrowBin16to8x8"); return;
    case Iop_NarrowBin32to16x4: vex_printf("NarrowBin32to16x4"); return;
    case Iop_NarrowBin64to32x4: vex_printf("NarrowBin64to32x4"); return;
    case Iop_InterleaveHI8x8: vex_printf("InterleaveHI8x8"); return;
    case Iop_InterleaveHI16x4: vex_printf("InterleaveHI16x4"); return;
    case Iop_InterleaveHI32x2: vex_printf("InterleaveHI32x2"); return;
    case Iop_InterleaveLO8x8: vex_printf("InterleaveLO8x8"); return;
    case Iop_InterleaveLO16x4: vex_printf("InterleaveLO16x4"); return;
    case Iop_InterleaveLO32x2: vex_printf("InterleaveLO32x2"); return;
    case Iop_CatOddLanes8x8: vex_printf("CatOddLanes8x8"); return;
    case Iop_CatOddLanes16x4: vex_printf("CatOddLanes16x4"); return;
    case Iop_CatEvenLanes8x8: vex_printf("CatEvenLanes8x8"); return;
    case Iop_CatEvenLanes16x4: vex_printf("CatEvenLanes16x4"); return;
    case Iop_InterleaveOddLanes8x8: vex_printf("InterleaveOddLanes8x8"); return;
    case Iop_InterleaveOddLanes16x4: vex_printf("InterleaveOddLanes16x4"); return;
    case Iop_InterleaveEvenLanes8x8: vex_printf("InterleaveEvenLanes8x8"); return;
    case Iop_InterleaveEvenLanes16x4: vex_printf("InterleaveEvenLanes16x4"); return;
    case Iop_Shl8x8: vex_printf("Shl8x8"); return;
    case Iop_Shl16x4: vex_printf("Shl16x4"); return;
    case Iop_Shl32x2: vex_printf("Shl32x2"); return;
    case Iop_Shr8x8: vex_printf("Shr8x8"); return;
    case Iop_Shr16x4: vex_printf("Shr16x4"); return;
    case Iop_Shr32x2: vex_printf("Shr32x2"); return;
    case Iop_QShl8x8: vex_printf("QShl8x8"); return;
    case Iop_QShl16x4: vex_printf("QShl16x4"); return;
    case Iop_QShl32x2: vex_printf("QShl32x2"); return;
    case Iop_QShl64x1: vex_printf("QShl64x1"); return;
    case Iop_QSal8x8: vex_printf("QSal8x8"); return;
    case Iop_QSal16x4: vex_printf("QSal16x4"); return;
    case Iop_QSal32x2: vex_printf("QSal32x2"); return;
    case Iop_QSal64x1: vex_printf("QSal64x1"); return;
    case Iop_QShlNsatUU8x8: vex_printf("QShlNsatUU8x8"); return;
    case Iop_QShlNsatUU16x4: vex_printf("QShlNsatUU16x4"); return;
    case Iop_QShlNsatUU32x2: vex_printf("QShlNsatUU32x2"); return;
    case Iop_QShlNsatUU64x1: vex_printf("QShlNsatUU64x1"); return;
    case Iop_QShlNsatSU8x8: vex_printf("QShlNsatSU8x8"); return;
    case Iop_QShlNsatSU16x4: vex_printf("QShlNsatSU16x4"); return;
    case Iop_QShlNsatSU32x2: vex_printf("QShlNsatSU32x2"); return;
    case Iop_QShlNsatSU64x1: vex_printf("QShlNsatSU64x1"); return;
    case Iop_QShlNsatSS8x8: vex_printf("QShlNsatSS8x8"); return;
    case Iop_QShlNsatSS16x4: vex_printf("QShlNsatSS16x4"); return;
    case Iop_QShlNsatSS32x2: vex_printf("QShlNsatSS32x2"); return;
    case Iop_QShlNsatSS64x1: vex_printf("QShlNsatSS64x1"); return;
    case Iop_Sar8x8: vex_printf("Sar8x8"); return;
    case Iop_Sar16x4: vex_printf("Sar16x4"); return;
    case Iop_Sar32x2: vex_printf("Sar32x2"); return;
    case Iop_Sal8x8: vex_printf("Sal8x8"); return;
    case Iop_Sal16x4: vex_printf("Sal16x4"); return;
    case Iop_Sal32x2: vex_printf("Sal32x2"); return;
    case Iop_Sal64x1: vex_printf("Sal64x1"); return;
    case Iop_Perm8x8: vex_printf("Perm8x8"); return;
    case Iop_PermOrZero8x8: vex_printf("PermOrZero8x8"); return;
    case Iop_Reverse8sIn16_x4: vex_printf("Reverse8sIn16_x4"); return;
    case Iop_Reverse8sIn32_x2: vex_printf("Reverse8sIn32_x2"); return;
    case Iop_Reverse16sIn32_x2: vex_printf("Reverse16sIn32_x2"); return;
    case Iop_Reverse8sIn64_x1: vex_printf("Reverse8sIn64_x1"); return;
    case Iop_Reverse16sIn64_x1: vex_printf("Reverse16sIn64_x1"); return;
    case Iop_Reverse32sIn64_x1: vex_printf("Reverse32sIn64_x1"); return;
    case Iop_Abs32Fx2: vex_printf("Abs32Fx2"); return;
    case Iop_GetMSBs8x8: vex_printf("GetMSBs8x8"); return;
    case Iop_GetMSBs8x16: vex_printf("GetMSBs8x16"); return;

    case Iop_CmpNEZ32x2: vex_printf("CmpNEZ32x2"); return;
    case Iop_CmpNEZ16x4: vex_printf("CmpNEZ16x4"); return;
    case Iop_CmpNEZ8x8:  vex_printf("CmpNEZ8x8"); return;

    case Iop_Add32Fx4:  vex_printf("Add32Fx4"); return;
    case Iop_Add32Fx2:  vex_printf("Add32Fx2"); return;
    case Iop_Add32F0x4: vex_printf("Add32F0x4"); return;
    case Iop_Add64Fx2:  vex_printf("Add64Fx2"); return;
    case Iop_Add64F0x2: vex_printf("Add64F0x2"); return;

    case Iop_Div32Fx4:  vex_printf("Div32Fx4"); return;
    case Iop_Div32F0x4: vex_printf("Div32F0x4"); return;
    case Iop_Div64Fx2:  vex_printf("Div64Fx2"); return;
    case Iop_Div64F0x2: vex_printf("Div64F0x2"); return;

    case Iop_Max32Fx8:  vex_printf("Max32Fx8"); return;
    case Iop_Max32Fx4:  vex_printf("Max32Fx4"); return;
    case Iop_Max32Fx2:  vex_printf("Max32Fx2"); return;
    case Iop_PwMax32Fx4:  vex_printf("PwMax32Fx4"); return;
    case Iop_PwMax32Fx2:  vex_printf("PwMax32Fx2"); return;
    case Iop_Max32F0x4: vex_printf("Max32F0x4"); return;
    case Iop_Max64Fx4:  vex_printf("Max64Fx4"); return;
    case Iop_Max64Fx2:  vex_printf("Max64Fx2"); return;
    case Iop_Max64F0x2: vex_printf("Max64F0x2"); return;

    case Iop_Min32Fx8:  vex_printf("Min32Fx8"); return;
    case Iop_Min32Fx4:  vex_printf("Min32Fx4"); return;
    case Iop_Min32Fx2:  vex_printf("Min32Fx2"); return;
    case Iop_PwMin32Fx4:  vex_printf("PwMin32Fx4"); return;
    case Iop_PwMin32Fx2:  vex_printf("PwMin32Fx2"); return;
    case Iop_Min32F0x4: vex_printf("Min32F0x4"); return;
    case Iop_Min64Fx4:  vex_printf("Min64Fx4"); return;
    case Iop_Min64Fx2:  vex_printf("Min64Fx2"); return;
    case Iop_Min64F0x2: vex_printf("Min64F0x2"); return;

    case Iop_Mul32Fx4:  vex_printf("Mul32Fx4"); return;
    case Iop_Mul32F0x4: vex_printf("Mul32F0x4"); return;
    case Iop_Mul64Fx2:  vex_printf("Mul64Fx2"); return;
    case Iop_Mul64F0x2: vex_printf("Mul64F0x2"); return;

    case Iop_RecipEst32Ux2: vex_printf("RecipEst32Ux2"); return;
    case Iop_RecipEst32Fx2: vex_printf("RecipEst32Fx2"); return;
    case Iop_RecipEst32Fx4: vex_printf("RecipEst32Fx4"); return;
    case Iop_RecipEst32Fx8: vex_printf("RecipEst32Fx8"); return;
    case Iop_RecipEst32Ux4: vex_printf("RecipEst32Ux4"); return;
    case Iop_RecipEst32F0x4: vex_printf("RecipEst32F0x4"); return;
    case Iop_RecipStep32Fx2: vex_printf("RecipStep32Fx2"); return;
    case Iop_RecipStep32Fx4: vex_printf("RecipStep32Fx4"); return;
    case Iop_RecipEst64Fx2: vex_printf("RecipEst64Fx2"); return;
    case Iop_RecipStep64Fx2: vex_printf("RecipStep64Fx2"); return;

    case Iop_Abs32Fx4:  vex_printf("Abs32Fx4"); return;
    case Iop_Abs64Fx2:  vex_printf("Abs64Fx2"); return;
    case Iop_RSqrtStep32Fx4:  vex_printf("RSqrtStep32Fx4"); return;
    case Iop_RSqrtStep64Fx2:  vex_printf("RSqrtStep64Fx2"); return;
    case Iop_RSqrtStep32Fx2:  vex_printf("RSqrtStep32Fx2"); return;
    case Iop_RSqrtEst64Fx2: vex_printf("RSqrtEst64Fx2"); return;

    case Iop_RSqrtEst32F0x4: vex_printf("RSqrtEst32F0x4"); return;
    case Iop_RSqrtEst32Fx8: vex_printf("RSqrtEst32Fx8"); return;

    case Iop_Sqrt32Fx4:  vex_printf("Sqrt32Fx4"); return;
    case Iop_Sqrt32F0x4: vex_printf("Sqrt32F0x4"); return;
    case Iop_Sqrt64Fx2:  vex_printf("Sqrt64Fx2"); return;
    case Iop_Sqrt64F0x2: vex_printf("Sqrt64F0x2"); return;
    case Iop_Sqrt32Fx8:  vex_printf("Sqrt32Fx8"); return;
    case Iop_Sqrt64Fx4:  vex_printf("Sqrt64Fx4"); return;

    case Iop_Scale2_32Fx4: vex_printf("Scale2_32Fx4"); return;
    case Iop_Scale2_64Fx2: vex_printf("Scale2_64Fx2"); return;
    case Iop_Log2_32Fx4: vex_printf("Log2_32Fx4"); return;
    case Iop_Log2_64Fx2: vex_printf("Log2_64Fx2"); return;
    case Iop_Exp2_32Fx4: vex_printf("Iop_Exp2_32Fx4"); return;

    case Iop_Sub32Fx4:  vex_printf("Sub32Fx4"); return;
    case Iop_Sub32Fx2:  vex_printf("Sub32Fx2"); return;
    case Iop_Sub32F0x4: vex_printf("Sub32F0x4"); return;
    case Iop_Sub64Fx2:  vex_printf("Sub64Fx2"); return;
    case Iop_Sub64F0x2: vex_printf("Sub64F0x2"); return;

    case Iop_CmpEQ32Fx4: vex_printf("CmpEQ32Fx4"); return;
    case Iop_CmpLT32Fx4: vex_printf("CmpLT32Fx4"); return;
    case Iop_CmpLE32Fx4: vex_printf("CmpLE32Fx4"); return;
    case Iop_CmpGT32Fx4: vex_printf("CmpGT32Fx4"); return;
    case Iop_CmpGE32Fx4: vex_printf("CmpGE32Fx4"); return;
    case Iop_CmpUN32Fx4: vex_printf("CmpUN32Fx4"); return;
    case Iop_CmpEQ64Fx2: vex_printf("CmpEQ64Fx2"); return;
    case Iop_CmpLT64Fx2: vex_printf("CmpLT64Fx2"); return;
    case Iop_CmpLE64Fx2: vex_printf("CmpLE64Fx2"); return;
    case Iop_CmpUN64Fx2: vex_printf("CmpUN64Fx2"); return;
    case Iop_CmpGT32Fx2: vex_printf("CmpGT32Fx2"); return;
    case Iop_CmpEQ32Fx2: vex_printf("CmpEQ32Fx2"); return;
    case Iop_CmpGE32Fx2: vex_printf("CmpGE32Fx2"); return;

    case Iop_CmpEQ32F0x4: vex_printf("CmpEQ32F0x4"); return;
    case Iop_CmpLT32F0x4: vex_printf("CmpLT32F0x4"); return;
    case Iop_CmpLE32F0x4: vex_printf("CmpLE32F0x4"); return;
    case Iop_CmpUN32F0x4: vex_printf("CmpUN32F0x4"); return;
    case Iop_CmpEQ64F0x2: vex_printf("CmpEQ64F0x2"); return;
    case Iop_CmpLT64F0x2: vex_printf("CmpLT64F0x2"); return;
    case Iop_CmpLE64F0x2: vex_printf("CmpLE64F0x2"); return;
    case Iop_CmpUN64F0x2: vex_printf("CmpUN64F0x2"); return;

    case Iop_Neg64Fx2: vex_printf("Neg64Fx2"); return;
    case Iop_Neg32Fx4: vex_printf("Neg32Fx4"); return;
    case Iop_Neg32Fx2: vex_printf("Neg32Fx2"); return;

    case Iop_F32x4_2toQ16x8: vex_printf("F32x4_2toQ16x8"); return;
    case Iop_F64x2_2toQ32x4: vex_printf("F64x2_2toQ32x4"); return;

    case Iop_V128to64:   vex_printf("V128to64");   return;
    case Iop_V128HIto64: vex_printf("V128HIto64"); return;
    case Iop_64HLtoV128: vex_printf("64HLtoV128"); return;

    case Iop_64UtoV128:   vex_printf("64UtoV128"); return;
    case Iop_SetV128lo64: vex_printf("SetV128lo64"); return;

    case Iop_ZeroHI64ofV128:  vex_printf("ZeroHI64ofV128"); return;
    case Iop_ZeroHI96ofV128:  vex_printf("ZeroHI96ofV128"); return;
    case Iop_ZeroHI112ofV128: vex_printf("ZeroHI112ofV128"); return;
    case Iop_ZeroHI120ofV128: vex_printf("ZeroHI120ofV128"); return;

    case Iop_32UtoV128:   vex_printf("32UtoV128"); return;
    case Iop_V128to32:    vex_printf("V128to32"); return;
    case Iop_SetV128lo32: vex_printf("SetV128lo32"); return;

    case Iop_Dup8x16: vex_printf("Dup8x16"); return;
    case Iop_Dup16x8: vex_printf("Dup16x8"); return;
    case Iop_Dup32x4: vex_printf("Dup32x4"); return;
    case Iop_Dup8x8: vex_printf("Dup8x8"); return;
    case Iop_Dup16x4: vex_printf("Dup16x4"); return;
    case Iop_Dup32x2: vex_printf("Dup32x2"); return;

    case Iop_NotV128:    vex_printf("NotV128"); return;
    case Iop_AndV128:    vex_printf("AndV128"); return;
    case Iop_OrV128:     vex_printf("OrV128");  return;
    case Iop_XorV128:    vex_printf("XorV128"); return;

    case Iop_CmpNEZ8x16: vex_printf("CmpNEZ8x16"); return;
    case Iop_CmpNEZ16x8: vex_printf("CmpNEZ16x8"); return;
    case Iop_CmpNEZ32x4: vex_printf("CmpNEZ32x4"); return;
    case Iop_CmpNEZ64x2: vex_printf("CmpNEZ64x2"); return;
    case Iop_CmpNEZ128x1: vex_printf("CmpNEZ128x1"); return;

    case Iop_Abs8x16: vex_printf("Abs8x16"); return;
    case Iop_Abs16x8: vex_printf("Abs16x8"); return;
    case Iop_Abs32x4: vex_printf("Abs32x4"); return;
    case Iop_Abs64x2: vex_printf("Abs64x2"); return;

    case Iop_Add8x16:   vex_printf("Add8x16"); return;
    case Iop_Add16x8:   vex_printf("Add16x8"); return;
    case Iop_Add32x4:   vex_printf("Add32x4"); return;
    case Iop_Add64x2:   vex_printf("Add64x2"); return;
    case Iop_Add128x1:  vex_printf("Add128x1"); return;
    case Iop_QAdd8Ux16: vex_printf("QAdd8Ux16"); return;
    case Iop_QAdd16Ux8: vex_printf("QAdd16Ux8"); return;
    case Iop_QAdd32Ux4: vex_printf("QAdd32Ux4"); return;
    case Iop_QAdd8Sx16: vex_printf("QAdd8Sx16"); return;
    case Iop_QAdd16Sx8: vex_printf("QAdd16Sx8"); return;
    case Iop_QAdd32Sx4: vex_printf("QAdd32Sx4"); return;
    case Iop_QAdd64Ux2: vex_printf("QAdd64Ux2"); return;
    case Iop_QAdd64Sx2: vex_printf("QAdd64Sx2"); return;

    case Iop_QAddExtUSsatSS8x16: vex_printf("QAddExtUSsatSS8x16"); return;
    case Iop_QAddExtUSsatSS16x8: vex_printf("QAddExtUSsatSS16x8"); return;
    case Iop_QAddExtUSsatSS32x4: vex_printf("QAddExtUSsatSS32x4"); return;
    case Iop_QAddExtUSsatSS64x2: vex_printf("QAddExtUSsatSS64x2"); return;
    case Iop_QAddExtSUsatUU8x16: vex_printf("QAddExtSUsatUU8x16"); return;
    case Iop_QAddExtSUsatUU16x8: vex_printf("QAddExtSUsatUU16x8"); return;
    case Iop_QAddExtSUsatUU32x4: vex_printf("QAddExtSUsatUU32x4"); return;
    case Iop_QAddExtSUsatUU64x2: vex_printf("QAddExtSUsatUU64x2"); return;

    case Iop_PwAdd8x16: vex_printf("PwAdd8x16"); return;
    case Iop_PwAdd16x8: vex_printf("PwAdd16x8"); return;
    case Iop_PwAdd32x4: vex_printf("PwAdd32x4"); return;
    case Iop_PwAddL8Ux16: vex_printf("PwAddL8Ux16"); return;
    case Iop_PwAddL16Ux8: vex_printf("PwAddL16Ux8"); return;
    case Iop_PwAddL32Ux4: vex_printf("PwAddL32Ux4"); return;
    case Iop_PwAddL64Ux2: vex_printf("PwAddL64Ux2"); return;
    case Iop_PwAddL8Sx16: vex_printf("PwAddL8Sx16"); return;
    case Iop_PwAddL16Sx8: vex_printf("PwAddL16Sx8"); return;
    case Iop_PwAddL32Sx4: vex_printf("PwAddL32Sx4"); return;
    case Iop_PwExtUSMulQAdd8x16: vex_printf("PwExtUSMulQAdd8x16"); return;

    case Iop_Sub8x16:   vex_printf("Sub8x16"); return;
    case Iop_Sub16x8:   vex_printf("Sub16x8"); return;
    case Iop_Sub32x4:   vex_printf("Sub32x4"); return;
    case Iop_Sub64x2:   vex_printf("Sub64x2"); return;
    case Iop_Sub128x1:  vex_printf("Sub128x1"); return;
    case Iop_QSub8Ux16: vex_printf("QSub8Ux16"); return;
    case Iop_QSub16Ux8: vex_printf("QSub16Ux8"); return;
    case Iop_QSub32Ux4: vex_printf("QSub32Ux4"); return;
    case Iop_QSub8Sx16: vex_printf("QSub8Sx16"); return;
    case Iop_QSub16Sx8: vex_printf("QSub16Sx8"); return;
    case Iop_QSub32Sx4: vex_printf("QSub32Sx4"); return;
    case Iop_QSub64Ux2: vex_printf("QSub64Ux2"); return;
    case Iop_QSub64Sx2: vex_printf("QSub64Sx2"); return;

    case Iop_Mul8x16:    vex_printf("Mul8x16"); return;
    case Iop_Mul16x8:    vex_printf("Mul16x8"); return;
    case Iop_Mul32x4:    vex_printf("Mul32x4"); return;
    case Iop_Mull8Ux8:    vex_printf("Mull8Ux8"); return;
    case Iop_Mull8Sx8:    vex_printf("Mull8Sx8"); return;
    case Iop_Mull16Ux4:    vex_printf("Mull16Ux4"); return;
    case Iop_Mull16Sx4:    vex_printf("Mull16Sx4"); return;
    case Iop_Mull32Ux2:    vex_printf("Mull32Ux2"); return;
    case Iop_Mull32Sx2:    vex_printf("Mull32Sx2"); return;
    case Iop_PolynomialMul8x16: vex_printf("PolynomialMul8x16"); return;
    case Iop_PolynomialMull8x8: vex_printf("PolynomialMull8x8"); return;
    case Iop_MulHi8Ux16: vex_printf("MulHi8Ux16"); return;
    case Iop_MulHi16Ux8: vex_printf("MulHi16Ux8"); return;
    case Iop_MulHi32Ux4: vex_printf("MulHi32Ux4"); return;
    case Iop_MulHi8Sx16: vex_printf("MulHi8Sx16"); return;
    case Iop_MulHi16Sx8: vex_printf("MulHi16Sx8"); return;
    case Iop_MulHi32Sx4: vex_printf("MulHi32Sx4"); return;
    case Iop_QDMulHi16Sx8: vex_printf("QDMulHi16Sx8"); return;
    case Iop_QDMulHi32Sx4: vex_printf("QDMulHi32Sx4"); return;
    case Iop_QRDMulHi16Sx8: vex_printf("QRDMulHi16Sx8"); return;
    case Iop_QRDMulHi32Sx4: vex_printf("QRDMulHi32Sx4"); return;

    case Iop_MullEven8Ux16: vex_printf("MullEven8Ux16"); return;
    case Iop_MullEven16Ux8: vex_printf("MullEven16Ux8"); return;
    case Iop_MullEven32Ux4: vex_printf("MullEven32Ux4"); return;
    case Iop_MullEven8Sx16: vex_printf("MullEven8Sx16"); return;
    case Iop_MullEven16Sx8: vex_printf("MullEven16Sx8"); return;
    case Iop_MullEven32Sx4: vex_printf("MullEven32Sx4"); return;

    case Iop_PolynomialMulAdd8x16:
        vex_printf("PolynomialMulAdd8x16"); return;
    case Iop_PolynomialMulAdd16x8:
        vex_printf("PolynomialMulAdd16x8"); return;
    case Iop_PolynomialMulAdd32x4:
        vex_printf("PolynomialMulAdd32x4"); return;
    case Iop_PolynomialMulAdd64x2:
        vex_printf("PolynomialMulAdd64x2"); return;

    case Iop_Avg8Ux16: vex_printf("Avg8Ux16"); return;
    case Iop_Avg16Ux8: vex_printf("Avg16Ux8"); return;
    case Iop_Avg32Ux4: vex_printf("Avg32Ux4"); return;
    case Iop_Avg64Ux2: vex_printf("Avg64Ux2"); return;
    case Iop_Avg8Sx16: vex_printf("Avg8Sx16"); return;
    case Iop_Avg16Sx8: vex_printf("Avg16Sx8"); return;
    case Iop_Avg32Sx4: vex_printf("Avg32Sx4"); return;
    case Iop_Avg64Sx2: vex_printf("Avg64Sx2"); return;

    case Iop_Max8Sx16: vex_printf("Max8Sx16"); return;
    case Iop_Max16Sx8: vex_printf("Max16Sx8"); return;
    case Iop_Max32Sx4: vex_printf("Max32Sx4"); return;
    case Iop_Max64Sx2: vex_printf("Max64Sx2"); return;
    case Iop_Max8Ux16: vex_printf("Max8Ux16"); return;
    case Iop_Max16Ux8: vex_printf("Max16Ux8"); return;
    case Iop_Max32Ux4: vex_printf("Max32Ux4"); return;
    case Iop_Max64Ux2: vex_printf("Max64Ux2"); return;

    case Iop_Min8Sx16: vex_printf("Min8Sx16"); return;
    case Iop_Min16Sx8: vex_printf("Min16Sx8"); return;
    case Iop_Min32Sx4: vex_printf("Min32Sx4"); return;
    case Iop_Min64Sx2: vex_printf("Min64Sx2"); return;
    case Iop_Min8Ux16: vex_printf("Min8Ux16"); return;
    case Iop_Min16Ux8: vex_printf("Min16Ux8"); return;
    case Iop_Min32Ux4: vex_printf("Min32Ux4"); return;
    case Iop_Min64Ux2: vex_printf("Min64Ux2"); return;

    case Iop_CmpEQ8x16:  vex_printf("CmpEQ8x16"); return;
    case Iop_CmpEQ16x8:  vex_printf("CmpEQ16x8"); return;
    case Iop_CmpEQ32x4:  vex_printf("CmpEQ32x4"); return;
    case Iop_CmpEQ64x2:  vex_printf("CmpEQ64x2"); return;
    case Iop_CmpGT8Sx16: vex_printf("CmpGT8Sx16"); return;
    case Iop_CmpGT16Sx8: vex_printf("CmpGT16Sx8"); return;
    case Iop_CmpGT32Sx4: vex_printf("CmpGT32Sx4"); return;
    case Iop_CmpGT64Sx2: vex_printf("CmpGT64Sx2"); return;
    case Iop_CmpGT8Ux16: vex_printf("CmpGT8Ux16"); return;
    case Iop_CmpGT16Ux8: vex_printf("CmpGT16Ux8"); return;
    case Iop_CmpGT32Ux4: vex_printf("CmpGT32Ux4"); return;
    case Iop_CmpGT64Ux2: vex_printf("CmpGT64Ux2"); return;

    case Iop_Cnt8x16: vex_printf("Cnt8x16"); return;
    case Iop_Clz8x16: vex_printf("Clz8x16"); return;
    case Iop_Clz16x8: vex_printf("Clz16x8"); return;
    case Iop_Clz32x4: vex_printf("Clz32x4"); return;
    case Iop_Clz64x2: vex_printf("Clz64x2"); return;
    case Iop_Cls8x16: vex_printf("Cls8x16"); return;
    case Iop_Cls16x8: vex_printf("Cls16x8"); return;
    case Iop_Cls32x4: vex_printf("Cls32x4"); return;
    case Iop_Ctz8x16: vex_printf("Iop_Ctz8x16"); return;
    case Iop_Ctz16x8: vex_printf("Iop_Ctz16x8"); return;
    case Iop_Ctz32x4: vex_printf("Iop_Ctz32x4"); return;
    case Iop_Ctz64x2: vex_printf("Iop_Ctz64x2"); return;

    case Iop_ShlV128: vex_printf("ShlV128"); return;
    case Iop_ShrV128: vex_printf("ShrV128"); return;
    case Iop_SarV128: vex_printf("SarV128"); return;

    case Iop_ShlN8x16: vex_printf("ShlN8x16"); return;
    case Iop_ShlN16x8: vex_printf("ShlN16x8"); return;
    case Iop_ShlN32x4: vex_printf("ShlN32x4"); return;
    case Iop_ShlN64x2: vex_printf("ShlN64x2"); return;
    case Iop_ShrN8x16: vex_printf("ShrN8x16"); return;
    case Iop_ShrN16x8: vex_printf("ShrN16x8"); return;
    case Iop_ShrN32x4: vex_printf("ShrN32x4"); return;
    case Iop_ShrN64x2: vex_printf("ShrN64x2"); return;
    case Iop_SarN8x16: vex_printf("SarN8x16"); return;
    case Iop_SarN16x8: vex_printf("SarN16x8"); return;
    case Iop_SarN32x4: vex_printf("SarN32x4"); return;
    case Iop_SarN64x2: vex_printf("SarN64x2"); return;

    case Iop_Shl8x16: vex_printf("Shl8x16"); return;
    case Iop_Shl16x8: vex_printf("Shl16x8"); return;
    case Iop_Shl32x4: vex_printf("Shl32x4"); return;
    case Iop_Shl64x2: vex_printf("Shl64x2"); return;
    case Iop_QSal8x16: vex_printf("QSal8x16"); return;
    case Iop_QSal16x8: vex_printf("QSal16x8"); return;
    case Iop_QSal32x4: vex_printf("QSal32x4"); return;
    case Iop_QSal64x2: vex_printf("QSal64x2"); return;
    case Iop_QShl8x16: vex_printf("QShl8x16"); return;
    case Iop_QShl16x8: vex_printf("QShl16x8"); return;
    case Iop_QShl32x4: vex_printf("QShl32x4"); return;
    case Iop_QShl64x2: vex_printf("QShl64x2"); return;
    case Iop_QShlNsatSS8x16: vex_printf("QShlNsatSS8x16"); return;
    case Iop_QShlNsatSS16x8: vex_printf("QShlNsatSS16x8"); return;
    case Iop_QShlNsatSS32x4: vex_printf("QShlNsatSS32x4"); return;
    case Iop_QShlNsatSS64x2: vex_printf("QShlNsatSS64x2"); return;
    case Iop_QShlNsatUU8x16: vex_printf("QShlNsatUU8x16"); return;
    case Iop_QShlNsatUU16x8: vex_printf("QShlNsatUU16x8"); return;
    case Iop_QShlNsatUU32x4: vex_printf("QShlNsatUU32x4"); return;
    case Iop_QShlNsatUU64x2: vex_printf("QShlNsatUU64x2"); return;
    case Iop_QShlNsatSU8x16: vex_printf("QShlNsatSU8x16"); return;
    case Iop_QShlNsatSU16x8: vex_printf("QShlNsatSU16x8"); return;
    case Iop_QShlNsatSU32x4: vex_printf("QShlNsatSU32x4"); return;
    case Iop_QShlNsatSU64x2: vex_printf("QShlNsatSU64x2"); return;
    case Iop_Shr8x16: vex_printf("Shr8x16"); return;
    case Iop_Shr16x8: vex_printf("Shr16x8"); return;
    case Iop_Shr32x4: vex_printf("Shr32x4"); return;
    case Iop_Shr64x2: vex_printf("Shr64x2"); return;
    case Iop_Sar8x16: vex_printf("Sar8x16"); return;
    case Iop_Sar16x8: vex_printf("Sar16x8"); return;
    case Iop_Sar32x4: vex_printf("Sar32x4"); return;
    case Iop_Sar64x2: vex_printf("Sar64x2"); return;
    case Iop_Sal8x16: vex_printf("Sal8x16"); return;
    case Iop_Sal16x8: vex_printf("Sal16x8"); return;
    case Iop_Sal32x4: vex_printf("Sal32x4"); return;
    case Iop_Sal64x2: vex_printf("Sal64x2"); return;
    case Iop_Rol8x16: vex_printf("Rol8x16"); return;
    case Iop_Rol16x8: vex_printf("Rol16x8"); return;
    case Iop_Rol32x4: vex_printf("Rol32x4"); return;
    case Iop_Rol64x2: vex_printf("Rol64x2"); return;

    case Iop_QandUQsh8x16: vex_printf("QandUQsh8x16"); return;
    case Iop_QandUQsh16x8: vex_printf("QandUQsh16x8"); return;
    case Iop_QandUQsh32x4: vex_printf("QandUQsh32x4"); return;
    case Iop_QandUQsh64x2: vex_printf("QandUQsh64x2"); return;
    case Iop_QandSQsh8x16: vex_printf("QandSQsh8x16"); return;
    case Iop_QandSQsh16x8: vex_printf("QandSQsh16x8"); return;
    case Iop_QandSQsh32x4: vex_printf("QandSQsh32x4"); return;
    case Iop_QandSQsh64x2: vex_printf("QandSQsh64x2"); return;
    case Iop_QandUQRsh8x16: vex_printf("QandUQRsh8x16"); return;
    case Iop_QandUQRsh16x8: vex_printf("QandUQRsh16x8"); return;
    case Iop_QandUQRsh32x4: vex_printf("QandUQRsh32x4"); return;
    case Iop_QandUQRsh64x2: vex_printf("QandUQRsh64x2"); return;
    case Iop_QandSQRsh8x16: vex_printf("QandSQRsh8x16"); return;
    case Iop_QandSQRsh16x8: vex_printf("QandSQRsh16x8"); return;
    case Iop_QandSQRsh32x4: vex_printf("QandSQRsh32x4"); return;
    case Iop_QandSQRsh64x2: vex_printf("QandSQRsh64x2"); return;

    case Iop_Sh8Sx16: vex_printf("Sh8Sx16"); return;
    case Iop_Sh16Sx8: vex_printf("Sh16Sx8"); return;
    case Iop_Sh32Sx4: vex_printf("Sh32Sx4"); return;
    case Iop_Sh64Sx2: vex_printf("Sh64Sx2"); return;
    case Iop_Sh8Ux16: vex_printf("Sh8Ux16"); return;
    case Iop_Sh16Ux8: vex_printf("Sh16Ux8"); return;
    case Iop_Sh32Ux4: vex_printf("Sh32Ux4"); return;
    case Iop_Sh64Ux2: vex_printf("Sh64Ux2"); return;
    case Iop_Rsh8Sx16: vex_printf("Rsh8Sx16"); return;
    case Iop_Rsh16Sx8: vex_printf("Rsh16Sx8"); return;
    case Iop_Rsh32Sx4: vex_printf("Rsh32Sx4"); return;
    case Iop_Rsh64Sx2: vex_printf("Rsh64Sx2"); return;
    case Iop_Rsh8Ux16: vex_printf("Rsh8Ux16"); return;
    case Iop_Rsh16Ux8: vex_printf("Rsh16Ux8"); return;
    case Iop_Rsh32Ux4: vex_printf("Rsh32Ux4"); return;
    case Iop_Rsh64Ux2: vex_printf("Rsh64Ux2"); return;

    case Iop_QandQShrNnarrow16Uto8Ux8:
        vex_printf("QandQShrNnarrow16Uto8Ux8"); return;
    case Iop_QandQShrNnarrow32Uto16Ux4:
        vex_printf("QandQShrNnarrow32Uto16Ux4"); return;
    case Iop_QandQShrNnarrow64Uto32Ux2:
        vex_printf("QandQShrNnarrow64Uto32Ux2"); return;
    case Iop_QandQSarNnarrow16Sto8Sx8:
        vex_printf("QandQSarNnarrow16Sto8Sx8"); return;
    case Iop_QandQSarNnarrow32Sto16Sx4:
        vex_printf("QandQSarNnarrow32Sto16Sx4"); return;
    case Iop_QandQSarNnarrow64Sto32Sx2:
        vex_printf("QandQSarNnarrow64Sto32Sx2"); return;
    case Iop_QandQSarNnarrow16Sto8Ux8:
        vex_printf("QandQSarNnarrow16Sto8Ux8"); return;
    case Iop_QandQSarNnarrow32Sto16Ux4:
        vex_printf("QandQSarNnarrow32Sto16Ux4"); return;
    case Iop_QandQSarNnarrow64Sto32Ux2:
        vex_printf("QandQSarNnarrow64Sto32Ux2"); return;
    case Iop_QandQRShrNnarrow16Uto8Ux8:
        vex_printf("QandQRShrNnarrow16Uto8Ux8"); return;
    case Iop_QandQRShrNnarrow32Uto16Ux4:
        vex_printf("QandQRShrNnarrow32Uto16Ux4"); return;
    case Iop_QandQRShrNnarrow64Uto32Ux2:
        vex_printf("QandQRShrNnarrow64Uto32Ux2"); return;
    case Iop_QandQRSarNnarrow16Sto8Sx8:
        vex_printf("QandQRSarNnarrow16Sto8Sx8"); return;
    case Iop_QandQRSarNnarrow32Sto16Sx4:
        vex_printf("QandQRSarNnarrow32Sto16Sx4"); return;
    case Iop_QandQRSarNnarrow64Sto32Sx2:
        vex_printf("QandQRSarNnarrow64Sto32Sx2"); return;
    case Iop_QandQRSarNnarrow16Sto8Ux8:
        vex_printf("QandQRSarNnarrow16Sto8Ux8"); return;
    case Iop_QandQRSarNnarrow32Sto16Ux4:
        vex_printf("QandQRSarNnarrow32Sto16Ux4"); return;
    case Iop_QandQRSarNnarrow64Sto32Ux2:
        vex_printf("QandQRSarNnarrow64Sto32Ux2"); return;

    case Iop_NarrowBin16to8x16:    vex_printf("NarrowBin16to8x16"); return;
    case Iop_NarrowBin32to16x8:    vex_printf("NarrowBin32to16x8"); return;
    case Iop_QNarrowBin16Uto8Ux16: vex_printf("QNarrowBin16Uto8Ux16"); return;
    case Iop_QNarrowBin32Sto16Ux8: vex_printf("QNarrowBin32Sto16Ux8"); return;
    case Iop_QNarrowBin16Sto8Ux16: vex_printf("QNarrowBin16Sto8Ux16"); return;
    case Iop_QNarrowBin32Uto16Ux8: vex_printf("QNarrowBin32Uto16Ux8"); return;
    case Iop_QNarrowBin16Sto8Sx16: vex_printf("QNarrowBin16Sto8Sx16"); return;
    case Iop_QNarrowBin32Sto16Sx8: vex_printf("QNarrowBin32Sto16Sx8"); return;
    case Iop_NarrowUn16to8x8:     vex_printf("NarrowUn16to8x8");  return;
    case Iop_NarrowUn32to16x4:    vex_printf("NarrowUn32to16x4"); return;
    case Iop_NarrowUn64to32x2:    vex_printf("NarrowUn64to32x2"); return;
    case Iop_QNarrowUn16Uto8Ux8:  vex_printf("QNarrowUn16Uto8Ux8");  return;
    case Iop_QNarrowUn32Uto16Ux4: vex_printf("QNarrowUn32Uto16Ux4"); return;
    case Iop_QNarrowUn64Uto32Ux2: vex_printf("QNarrowUn64Uto32Ux2"); return;
    case Iop_QNarrowUn16Sto8Sx8:  vex_printf("QNarrowUn16Sto8Sx8");  return;
    case Iop_QNarrowUn32Sto16Sx4: vex_printf("QNarrowUn32Sto16Sx4"); return;
    case Iop_QNarrowUn64Sto32Sx2: vex_printf("QNarrowUn64Sto32Sx2"); return;
    case Iop_QNarrowUn16Sto8Ux8:  vex_printf("QNarrowUn16Sto8Ux8");  return;
    case Iop_QNarrowUn32Sto16Ux4: vex_printf("QNarrowUn32Sto16Ux4"); return;
    case Iop_QNarrowUn64Sto32Ux2: vex_printf("QNarrowUn64Sto32Ux2"); return;
    case Iop_Widen8Uto16x8:  vex_printf("Widen8Uto16x8");  return;
    case Iop_Widen16Uto32x4: vex_printf("Widen16Uto32x4"); return;
    case Iop_Widen32Uto64x2: vex_printf("Widen32Uto64x2"); return;
    case Iop_Widen8Sto16x8:  vex_printf("Widen8Sto16x8");  return;
    case Iop_Widen16Sto32x4: vex_printf("Widen16Sto32x4"); return;
    case Iop_Widen32Sto64x2: vex_printf("Widen32Sto64x2"); return;

    case Iop_InterleaveHI8x16: vex_printf("InterleaveHI8x16"); return;
    case Iop_InterleaveHI16x8: vex_printf("InterleaveHI16x8"); return;
    case Iop_InterleaveHI32x4: vex_printf("InterleaveHI32x4"); return;
    case Iop_InterleaveHI64x2: vex_printf("InterleaveHI64x2"); return;
    case Iop_InterleaveLO8x16: vex_printf("InterleaveLO8x16"); return;
    case Iop_InterleaveLO16x8: vex_printf("InterleaveLO16x8"); return;
    case Iop_InterleaveLO32x4: vex_printf("InterleaveLO32x4"); return;
    case Iop_InterleaveLO64x2: vex_printf("InterleaveLO64x2"); return;

    case Iop_CatOddLanes8x16: vex_printf("CatOddLanes8x16"); return;
    case Iop_CatOddLanes16x8: vex_printf("CatOddLanes16x8"); return;
    case Iop_CatOddLanes32x4: vex_printf("CatOddLanes32x4"); return;
    case Iop_CatEvenLanes8x16: vex_printf("CatEvenLanes8x16"); return;
    case Iop_CatEvenLanes16x8: vex_printf("CatEvenLanes16x8"); return;
    case Iop_CatEvenLanes32x4: vex_printf("CatEvenLanes32x4"); return;

    case Iop_InterleaveOddLanes8x16: vex_printf("InterleaveOddLanes8x16"); return;
    case Iop_InterleaveOddLanes16x8: vex_printf("InterleaveOddLanes16x8"); return;
    case Iop_InterleaveOddLanes32x4: vex_printf("InterleaveOddLanes32x4"); return;
    case Iop_InterleaveEvenLanes8x16: vex_printf("InterleaveEvenLanes8x16"); return;
    case Iop_InterleaveEvenLanes16x8: vex_printf("InterleaveEvenLanes16x8"); return;
    case Iop_InterleaveEvenLanes32x4: vex_printf("InterleaveEvenLanes32x4"); return;
    case Iop_PackOddLanes8x16: vex_printf("InterleavePackOddLanes8x16"); return;
    case Iop_PackOddLanes16x8: vex_printf("InterleavePackOddLanes16x8"); return;
    case Iop_PackOddLanes32x4: vex_printf("InterleavePackOddLanes32x4"); return;
    case Iop_PackEvenLanes8x16: vex_printf("InterleavePackEvenLanes8x16"); return;
    case Iop_PackEvenLanes16x8: vex_printf("InterleavePackEvenLanes16x8"); return;
    case Iop_PackEvenLanes32x4: vex_printf("InterleavePackEvenLanes32x4"); return;

    case Iop_GetElem8x16: vex_printf("GetElem8x16"); return;
    case Iop_GetElem16x8: vex_printf("GetElem16x8"); return;
    case Iop_GetElem32x4: vex_printf("GetElem32x4"); return;
    case Iop_GetElem64x2: vex_printf("GetElem64x2"); return;

    case Iop_SetElem8x16: vex_printf("SetElem8x16"); return;
    case Iop_SetElem16x8: vex_printf("SetElem16x8"); return;
    case Iop_SetElem32x4: vex_printf("SetElem32x4"); return;
    case Iop_SetElem64x2: vex_printf("SetElem64x2"); return;

    case Iop_GetElem8x8: vex_printf("GetElem8x8"); return;
    case Iop_GetElem16x4: vex_printf("GetElem16x4"); return;
    case Iop_GetElem32x2: vex_printf("GetElem32x2"); return;
    case Iop_SetElem8x8: vex_printf("SetElem8x8"); return;
    case Iop_SetElem16x4: vex_printf("SetElem16x4"); return;
    case Iop_SetElem32x2: vex_printf("SetElem32x2"); return;

    case Iop_Slice64: vex_printf("Slice64"); return;
    case Iop_SliceV128: vex_printf("SliceV128"); return;

    case Iop_Perm8x16: vex_printf("Perm8x16"); return;
    case Iop_PermOrZero8x16: vex_printf("PermOrZero8x16"); return;
    case Iop_Perm32x4: vex_printf("Perm32x4"); return;
    case Iop_Perm8x16x2: vex_printf("Perm8x16x2"); return;
    case Iop_Reverse8sIn16_x8: vex_printf("Reverse8sIn16_x8"); return;
    case Iop_Reverse8sIn32_x4: vex_printf("Reverse8sIn32_x4"); return;
    case Iop_Reverse16sIn32_x4: vex_printf("Reverse16sIn32_x4"); return;
    case Iop_Reverse8sIn64_x2: vex_printf("Reverse8sIn64_x2"); return;
    case Iop_Reverse16sIn64_x2: vex_printf("Reverse16sIn64_x2"); return;
    case Iop_Reverse32sIn64_x2: vex_printf("Reverse32sIn64_x2"); return;
    case Iop_Reverse1sIn8_x16: vex_printf("Reverse1sIn8_x16"); return;

    case Iop_F32ToFixed32Ux4_RZ: vex_printf("F32ToFixed32Ux4_RZ"); return;
    case Iop_F32ToFixed32Sx4_RZ: vex_printf("F32ToFixed32Sx4_RZ"); return;
    case Iop_Fixed32UToF32x4_RN: vex_printf("Fixed32UToF32x4_RN"); return;
    case Iop_Fixed32SToF32x4_RN: vex_printf("Fixed32SToF32x4_RN"); return;
    case Iop_F32ToFixed32Ux2_RZ: vex_printf("F32ToFixed32Ux2_RZ"); return;
    case Iop_F32ToFixed32Sx2_RZ: vex_printf("F32ToFixed32Sx2_RZ"); return;
    case Iop_Fixed32UToF32x2_RN: vex_printf("Fixed32UToF32x2_RN"); return;
    case Iop_Fixed32SToF32x2_RN: vex_printf("Fixed32SToF32x2_RN"); return;

    case Iop_D32toD64:  vex_printf("D32toD64");   return;
    case Iop_D64toD32:  vex_printf("D64toD32");   return;
    case Iop_AddD64:  vex_printf("AddD64");   return;
    case Iop_SubD64:  vex_printf("SubD64");   return;
    case Iop_MulD64:  vex_printf("MulD64");   return;
    case Iop_DivD64:  vex_printf("DivD64");   return;
    case Iop_ShlD64:  vex_printf("ShlD64"); return;
    case Iop_ShrD64:  vex_printf("ShrD64"); return;
    case Iop_D64toI32S:  vex_printf("D64toI32S");  return;
    case Iop_D64toI32U:  vex_printf("D64toI32U");  return;
    case Iop_D64toI64S:  vex_printf("D64toI64S");  return;
    case Iop_D64toI64U:  vex_printf("D64toI64U");  return;
    case Iop_I32StoD64:  vex_printf("I32StoD64");  return;
    case Iop_I32UtoD64:  vex_printf("I32UtoD64");  return;
    case Iop_I64StoD64:  vex_printf("I64StoD64");  return;
    case Iop_I64UtoD64:  vex_printf("I64UtoD64");  return;
    case Iop_I32StoD128: vex_printf("I32StoD128"); return;
    case Iop_I32UtoD128: vex_printf("I32UtoD128"); return;
    case Iop_I64StoD128: vex_printf("I64StoD128"); return;
    case Iop_I64UtoD128: vex_printf("I64UtoD128"); return;
    case Iop_D64toD128:  vex_printf("D64toD128");  return;
    case Iop_D128toD64:  vex_printf("D128toD64");  return;
    case Iop_D128toI32S: vex_printf("D128toI32S"); return;
    case Iop_D128toI32U: vex_printf("D128toI32U"); return;
    case Iop_D128toI64S: vex_printf("D128toI64S"); return;
    case Iop_D128toI64U: vex_printf("D128toI64U"); return;
    case Iop_F32toD32:   vex_printf("F32toD32");   return;
    case Iop_F32toD64:   vex_printf("F32toD64");   return;
    case Iop_F32toD128:  vex_printf("F32toD128");  return;
    case Iop_F64toD32:   vex_printf("F64toD32");   return;
    case Iop_F64toD64:   vex_printf("F64toD64");   return;
    case Iop_F64toD128:  vex_printf("F64toD128");  return;
    case Iop_F128toD32:  vex_printf("F128toD32");  return;
    case Iop_F128toD64:  vex_printf("F128toD64");  return;
    case Iop_F128toD128: vex_printf("F128toD128"); return;
    case Iop_D32toF32:   vex_printf("D32toF32");   return;
    case Iop_D32toF64:   vex_printf("D32toF64");   return;
    case Iop_D32toF128:  vex_printf("D32toF128");  return;
    case Iop_D64toF32:   vex_printf("D64toF32");   return;
    case Iop_D64toF64:   vex_printf("D64toF64");   return;
    case Iop_D64toF128:  vex_printf("D64toF128");  return;
    case Iop_D128toF32:  vex_printf("D128toF32");  return;
    case Iop_D128toF64:  vex_printf("D128toF64");  return;
    case Iop_D128toF128: vex_printf("D128toF128"); return;
    case Iop_AddD128: vex_printf("AddD128");  return;
    case Iop_SubD128: vex_printf("SubD128");  return;
    case Iop_MulD128: vex_printf("MulD128");  return;
    case Iop_DivD128: vex_printf("DivD128");  return;
    case Iop_ShlD128: vex_printf("ShlD128");  return;
    case Iop_ShrD128: vex_printf("ShrD128");  return;
    case Iop_RoundD64toInt:  vex_printf("RoundD64toInt");  return;
    case Iop_RoundD128toInt: vex_printf("RoundD128toInt"); return;
    case Iop_QuantizeD64:    vex_printf("QuantizeD64");    return;
    case Iop_QuantizeD128:   vex_printf("QuantizeD128");   return;
    case Iop_ExtractExpD64:  vex_printf("ExtractExpD64");  return;
    case Iop_ExtractExpD128: vex_printf("ExtractExpD128"); return;
    case Iop_ExtractSigD64:  vex_printf("ExtractSigD64");  return;
    case Iop_ExtractSigD128: vex_printf("ExtractSigD128"); return;
    case Iop_InsertExpD64:   vex_printf("InsertExpD64");   return;
    case Iop_InsertExpD128:  vex_printf("InsertExpD128");  return;
    case Iop_CmpD64:         vex_printf("CmpD64");     return;
    case Iop_CmpD128:        vex_printf("CmpD128");    return;
    case Iop_CmpExpD64:      vex_printf("CmpExpD64");  return;
    case Iop_CmpExpD128:     vex_printf("CmpExpD128"); return;
    case Iop_D64HLtoD128: vex_printf("D64HLtoD128");   return;
    case Iop_D128HItoD64: vex_printf("D128HItoD64");   return;
    case Iop_D128LOtoD64: vex_printf("D128LOtoD64");   return;
    case Iop_SignificanceRoundD64: vex_printf("SignificanceRoundD64");
        return;
    case Iop_SignificanceRoundD128: vex_printf("SignificanceRoundD128");
        return;
    case Iop_ReinterpI64asD64: vex_printf("ReinterpI64asD64"); return;
    case Iop_ReinterpD64asI64: vex_printf("ReinterpD64asI64"); return;
    case Iop_V256to64_0: vex_printf("V256to64_0"); return;
    case Iop_V256to64_1: vex_printf("V256to64_1"); return;
    case Iop_V256to64_2: vex_printf("V256to64_2"); return;
    case Iop_V256to64_3: vex_printf("V256to64_3"); return;
    case Iop_64x4toV256: vex_printf("64x4toV256"); return;
    case Iop_V256toV128_0: vex_printf("V256toV128_0"); return;
    case Iop_V256toV128_1: vex_printf("V256toV128_1"); return;
    case Iop_V128HLtoV256: vex_printf("V128HLtoV256"); return;
    case Iop_DPBtoBCD: vex_printf("DPBtoBCD"); return;
    case Iop_BCDtoDPB: vex_printf("BCDtoDPB"); return;
    case Iop_Add64Fx4: vex_printf("Add64Fx4"); return;
    case Iop_Sub64Fx4: vex_printf("Sub64Fx4"); return;
    case Iop_Mul64Fx4: vex_printf("Mul64Fx4"); return;
    case Iop_Div64Fx4: vex_printf("Div64Fx4"); return;
    case Iop_Add32Fx8: vex_printf("Add32Fx8"); return;
    case Iop_Sub32Fx8: vex_printf("Sub32Fx8"); return;
    case Iop_Mul32Fx8: vex_printf("Mul32Fx8"); return;
    case Iop_Div32Fx8: vex_printf("Div32Fx8"); return;
    case Iop_I32StoF32x8: vex_printf("I32StoF32x8"); return;
    case Iop_F32toI32Sx8: vex_printf("F32toI32Sx8"); return;
    case Iop_F32toF16x8: vex_printf("F32toF16x8"); return;
    case Iop_F16toF32x8: vex_printf("F16toF32x8"); return;
    case Iop_AndV256: vex_printf("AndV256"); return;
    case Iop_OrV256:  vex_printf("OrV256"); return;
    case Iop_XorV256: vex_printf("XorV256"); return;
    case Iop_NotV256: vex_printf("NotV256"); return;
    case Iop_CmpNEZ64x4: vex_printf("CmpNEZ64x4"); return;
    case Iop_CmpNEZ32x8: vex_printf("CmpNEZ32x8"); return;
    case Iop_CmpNEZ16x16: vex_printf("CmpNEZ16x16"); return;
    case Iop_CmpNEZ8x32: vex_printf("CmpNEZ8x32"); return;

    case Iop_Add8x32:   vex_printf("Add8x32"); return;
    case Iop_Add16x16:  vex_printf("Add16x16"); return;
    case Iop_Add32x8:   vex_printf("Add32x8"); return;
    case Iop_Add64x4:   vex_printf("Add64x4"); return;
    case Iop_Sub8x32:   vex_printf("Sub8x32"); return;
    case Iop_Sub16x16:  vex_printf("Sub16x16"); return;
    case Iop_Sub32x8:   vex_printf("Sub32x8"); return;
    case Iop_Sub64x4:   vex_printf("Sub64x4"); return;
    case Iop_QAdd8Ux32: vex_printf("QAdd8Ux32"); return;
    case Iop_QAdd16Ux16: vex_printf("QAdd16Ux16"); return;
    case Iop_QAdd8Sx32: vex_printf("QAdd8Sx32"); return;
    case Iop_QAdd16Sx16: vex_printf("QAdd16Sx16"); return;
    case Iop_QSub8Ux32: vex_printf("QSub8Ux32"); return;
    case Iop_QSub16Ux16: vex_printf("QSub16Ux16"); return;
    case Iop_QSub8Sx32: vex_printf("QSub8Sx32"); return;
    case Iop_QSub16Sx16: vex_printf("QSub16Sx16"); return;

    case Iop_Mul16x16:    vex_printf("Mul16x16"); return;
    case Iop_Mul32x8:     vex_printf("Mul32x8"); return;
    case Iop_MulHi16Ux16: vex_printf("MulHi16Ux16"); return;
    case Iop_MulHi16Sx16: vex_printf("MulHi16Sx16"); return;

    case Iop_Avg8Ux32:  vex_printf("Avg8Ux32"); return;
    case Iop_Avg16Ux16: vex_printf("Avg16Ux16"); return;

    case Iop_Max8Sx32:  vex_printf("Max8Sx32"); return;
    case Iop_Max16Sx16: vex_printf("Max16Sx16"); return;
    case Iop_Max32Sx8:  vex_printf("Max32Sx8"); return;
    case Iop_Max8Ux32:  vex_printf("Max8Ux32"); return;
    case Iop_Max16Ux16: vex_printf("Max16Ux16"); return;
    case Iop_Max32Ux8:  vex_printf("Max32Ux8"); return;

    case Iop_Min8Sx32:  vex_printf("Min8Sx32"); return;
    case Iop_Min16Sx16: vex_printf("Min16Sx16"); return;
    case Iop_Min32Sx8:  vex_printf("Min32Sx8"); return;
    case Iop_Min8Ux32:  vex_printf("Min8Ux32"); return;
    case Iop_Min16Ux16: vex_printf("Min16Ux16"); return;
    case Iop_Min32Ux8:  vex_printf("Min32Ux8"); return;

    case Iop_CmpEQ8x32:   vex_printf("CmpEQ8x32"); return;
    case Iop_CmpEQ16x16:  vex_printf("CmpEQ16x16"); return;
    case Iop_CmpEQ32x8:   vex_printf("CmpEQ32x8"); return;
    case Iop_CmpEQ64x4:   vex_printf("CmpEQ64x4"); return;
    case Iop_CmpGT8Sx32:  vex_printf("CmpGT8Sx32"); return;
    case Iop_CmpGT16Sx16: vex_printf("CmpGT16Sx16"); return;
    case Iop_CmpGT32Sx8:  vex_printf("CmpGT32Sx8"); return;
    case Iop_CmpGT64Sx4:  vex_printf("CmpGT64Sx4"); return;

    case Iop_ShlN16x16:  vex_printf("ShlN16x16"); return;
    case Iop_ShlN32x8:   vex_printf("ShlN32x8"); return;
    case Iop_ShlN64x4:   vex_printf("ShlN64x4"); return;
    case Iop_ShrN16x16:  vex_printf("ShrN16x16"); return;
    case Iop_ShrN32x8:   vex_printf("ShrN32x8"); return;
    case Iop_ShrN64x4:   vex_printf("ShrN64x4"); return;
    case Iop_SarN16x16:  vex_printf("SarN16x16"); return;
    case Iop_SarN32x8:   vex_printf("SarN32x8"); return;

    case Iop_Perm32x8:   vex_printf("Perm32x8"); return;

    case Iop_CipherV128:   vex_printf("CipherV128"); return;
    case Iop_CipherLV128:  vex_printf("CipherLV128"); return;
    case Iop_NCipherV128:  vex_printf("NCipherV128"); return;
    case Iop_NCipherLV128: vex_printf("NCipherLV128"); return;
    case Iop_CipherSV128:  vex_printf("CipherSV128"); return;

    case Iop_SHA256:  vex_printf("SHA256"); return;
    case Iop_SHA512:  vex_printf("SHA512"); return;
    case Iop_BCDAdd:  vex_printf("BCDAdd"); return;
    case Iop_BCDSub:  vex_printf("BCDSub"); return;
    case Iop_I128StoBCD128:  vex_printf("bcdcfsq."); return;
    case Iop_BCD128toI128S:  vex_printf("bcdctsq."); return;
    case Iop_Rotx32:  vex_printf("bitswap"); return;
    case Iop_Rotx64:  vex_printf("dbitswap"); return;

    case Iop_PwBitMtxXpose64x2: vex_printf("BitMatrixTranspose64x2"); return;

    default: VPANIC("ppIROp(1)");
    }

    vassert(str);
    switch (op - base) {
    case 0: vex_printf("%s", str); vex_printf("8"); break;
    case 1: vex_printf("%s", str); vex_printf("16"); break;
    case 2: vex_printf("%s", str); vex_printf("32"); break;
    case 3: vex_printf("%s", str); vex_printf("64"); break;
    default: VPANIC("ppIROp(2)");
    }
}

 void ppIR::ppIRExpr(const IRExpr* e)
{
    Int i;
    switch (e->tag) {
    case Iex_Binder:
        vex_printf("BIND-%d", e->Iex.Binder.binder);
        break;
    case Iex_Get:
        vex_printf("GET:");
        ppIRType(e->Iex.Get.ty);
        vex_printf("(%d)", e->Iex.Get.offset);
        break;
    case Iex_GetI:
        vex_printf("GETI");
        ppIRRegArray(e->Iex.GetI.descr);
        vex_printf("[");
        ppIRExpr(e->Iex.GetI.ix);
        vex_printf(",%d]", e->Iex.GetI.bias);
        break;
    case Iex_RdTmp:
        ppIRTemp(e->Iex.RdTmp.tmp);
        break;
    case Iex_Qop: {
        const IRQop* qop = e->Iex.Qop.details;
        ppIROp(qop->op);
        vex_printf("(");
        ppIRExpr(qop->arg1);
        vex_printf(",");
        ppIRExpr(qop->arg2);
        vex_printf(",");
        ppIRExpr(qop->arg3);
        vex_printf(",");
        ppIRExpr(qop->arg4);
        vex_printf(")");
        break;
    }
    case Iex_Triop: {
        const IRTriop* triop = e->Iex.Triop.details;
        ppIROp(triop->op);
        vex_printf("(");
        ppIRExpr(triop->arg1);
        vex_printf(",");
        ppIRExpr(triop->arg2);
        vex_printf(",");
        ppIRExpr(triop->arg3);
        vex_printf(")");
        break;
    }
    case Iex_Binop:
        ppIROp(e->Iex.Binop.op);
        vex_printf("(");
        ppIRExpr(e->Iex.Binop.arg1);
        vex_printf(",");
        ppIRExpr(e->Iex.Binop.arg2);
        vex_printf(")");
        break;
    case Iex_Unop:
        ppIROp(e->Iex.Unop.op);
        vex_printf("(");
        ppIRExpr(e->Iex.Unop.arg);
        vex_printf(")");
        break;
    case Iex_Load:
        vex_printf("LD%s:", e->Iex.Load.end == Iend_LE ? "le" : "be");
        ppIRType(e->Iex.Load.ty);
        vex_printf("(");
        ppIRExpr(e->Iex.Load.addr);
        vex_printf(")");
        break;
    case Iex_Const:
        ppIRConst(e->Iex.Const.con);
        break;
    case Iex_CCall:
        ppIRCallee(e->Iex.CCall.cee);
        vex_printf("(");
        for (i = 0; e->Iex.CCall.args[i] != NULL; i++) {
            IRExpr* arg = e->Iex.CCall.args[i];
            ppIRExpr(arg);

            if (e->Iex.CCall.args[i + 1] != NULL) {
                vex_printf(",");
            }
        }
        vex_printf("):");
        ppIRType(e->Iex.CCall.retty);
        break;
    case Iex_ITE:
        vex_printf("ITE(");
        ppIRExpr(e->Iex.ITE.cond);
        vex_printf(",");
        ppIRExpr(e->Iex.ITE.iftrue);
        vex_printf(",");
        ppIRExpr(e->Iex.ITE.iffalse);
        vex_printf(")");
        break;
    case Iex_VECRET:
        vex_printf("VECRET");
        break;
    case Iex_GSPTR:
        vex_printf("GSPTR");
        break;
    default:
        VPANIC("ppIRExpr");
    }
}

 void ppIR::ppIREffect(IREffect fx)
{
    switch (fx) {
    case Ifx_None:   vex_printf("noFX"); return;
    case Ifx_Read:   vex_printf("RdFX"); return;
    case Ifx_Write:  vex_printf("WrFX"); return;
    case Ifx_Modify: vex_printf("MoFX"); return;
    default: VPANIC("ppIREffect");
    }
}

 void ppIR::ppIRDirty(const IRDirty* d)
{
    Int i;
    if (d->tmp != IRTemp_INVALID) {
        ppIRTemp(d->tmp);
        vex_printf(" = ");
    }
    vex_printf("DIRTY ");
    ppIRExpr(d->guard);
    if (d->mFx != Ifx_None) {
        vex_printf(" ");
        ppIREffect(d->mFx);
        vex_printf("-mem(");
        ppIRExpr(d->mAddr);
        vex_printf(",%d)", d->mSize);
    }
    for (i = 0; i < d->nFxState; i++) {
        vex_printf(" ");
        ppIREffect(d->fxState[i].fx);
        vex_printf("-gst(%u,%u", (UInt)d->fxState[i].offset,
            (UInt)d->fxState[i].size);
        if (d->fxState[i].nRepeats > 0) {
            vex_printf(",reps%u,step%u", (UInt)d->fxState[i].nRepeats,
                (UInt)d->fxState[i].repeatLen);
        }
        vex_printf(")");
    }
    vex_printf(" ::: ");
    ppIRCallee(d->cee);
    vex_printf("(");
    for (i = 0; d->args[i] != NULL; i++) {
        IRExpr* arg = d->args[i];
        ppIRExpr(arg);

        if (d->args[i + 1] != NULL) {
            vex_printf(",");
        }
    }
    vex_printf(")");
}

 void ppIR::ppIRCAS(const IRCAS* cas)
{
    /* Print even structurally invalid constructions, as an aid to
    debugging. */
    if (cas->oldHi != IRTemp_INVALID) {
        ppIRTemp(cas->oldHi);
        vex_printf(",");
    }
    ppIRTemp(cas->oldLo);
    vex_printf(" = CAS%s(", cas->end == Iend_LE ? "le" : "be");
    ppIRExpr(cas->addr);
    vex_printf("::");
    if (cas->expdHi) {
        ppIRExpr(cas->expdHi);
        vex_printf(",");
    }
    ppIRExpr(cas->expdLo);
    vex_printf("->");
    if (cas->dataHi) {
        ppIRExpr(cas->dataHi);
        vex_printf(",");
    }
    ppIRExpr(cas->dataLo);
    vex_printf(")");
}

 void ppIR::ppIRPutI(const IRPutI* puti)
{
    vex_printf("PUTI");
    ppIRRegArray(puti->descr);
    vex_printf("[");
    ppIRExpr(puti->ix);
    vex_printf(",%d] = ", puti->bias);
    ppIRExpr(puti->data);
}

 void ppIR::ppIRStoreG(const IRStoreG* sg)
{
    vex_printf("if (");
    ppIRExpr(sg->guard);
    vex_printf(") { ST%s(", sg->end == Iend_LE ? "le" : "be");
    ppIRExpr(sg->addr);
    vex_printf(") = ");
    ppIRExpr(sg->data);
    vex_printf(" }");
}

 void ppIR::ppIRLoadGOp(IRLoadGOp cvt)
{
    switch (cvt) {
    case ILGop_INVALID:   vex_printf("ILGop_INVALID"); break;
    case ILGop_IdentV128: vex_printf("IdentV128"); break;
    case ILGop_Ident64:   vex_printf("Ident64"); break;
    case ILGop_Ident32:   vex_printf("Ident32"); break;
    case ILGop_16Uto32:   vex_printf("16Uto32"); break;
    case ILGop_16Sto32:   vex_printf("16Sto32"); break;
    case ILGop_8Uto32:    vex_printf("8Uto32"); break;
    case ILGop_8Sto32:    vex_printf("8Sto32"); break;
    default: VPANIC("ppIRLoadGOp");
    }
}

 void ppIR::ppIRLoadG(const IRLoadG* lg)
{
    ppIRTemp(lg->dst);
    vex_printf(" = if-strict (");
    ppIRExpr(lg->guard);
    vex_printf(") ");
    ppIRLoadGOp(lg->cvt);
    vex_printf("(LD%s(", lg->end == Iend_LE ? "le" : "be");
    ppIRExpr(lg->addr);
    vex_printf(")) else ");
    ppIRExpr(lg->alt);
}

 void ppIR::ppIRJumpKind(IRJumpKind kind)
{
    switch (kind) {
    case Ijk_Boring:        vex_printf("Boring"); break;
    case Ijk_Call:          vex_printf("Call"); break;
    case Ijk_Ret:           vex_printf("Return"); break;
    case Ijk_ClientReq:     vex_printf("ClientReq"); break;
    case Ijk_Yield:         vex_printf("Yield"); break;
    case Ijk_EmWarn:        vex_printf("EmWarn"); break;
    case Ijk_EmFail:        vex_printf("EmFail"); break;
    case Ijk_NoDecode:      vex_printf("NoDecode"); break;
    case Ijk_MapFail:       vex_printf("MapFail"); break;
    case Ijk_InvalICache:   vex_printf("InvalICache"); break;
    case Ijk_FlushDCache:   vex_printf("FlushDCache"); break;
    case Ijk_NoRedir:       vex_printf("NoRedir"); break;
    case Ijk_SigILL:        vex_printf("SigILL"); break;
    case Ijk_SigTRAP:       vex_printf("SigTRAP"); break;
    case Ijk_SigSEGV:       vex_printf("SigSEGV"); break;
    case Ijk_SigBUS:        vex_printf("SigBUS"); break;
    case Ijk_SigFPE:        vex_printf("SigFPE"); break;
    case Ijk_SigFPE_IntDiv: vex_printf("SigFPE_IntDiv"); break;
    case Ijk_SigFPE_IntOvf: vex_printf("SigFPE_IntOvf"); break;
    case Ijk_Sys_syscall:   vex_printf("Sys_syscall"); break;
    case Ijk_Sys_int32:     vex_printf("Sys_int32"); break;
    case Ijk_Sys_int128:    vex_printf("Sys_int128"); break;
    case Ijk_Sys_int129:    vex_printf("Sys_int129"); break;
    case Ijk_Sys_int130:    vex_printf("Sys_int130"); break;
    case Ijk_Sys_int145:    vex_printf("Sys_int145"); break;
    case Ijk_Sys_int210:    vex_printf("Sys_int210"); break;
    case Ijk_Sys_sysenter:  vex_printf("Sys_sysenter"); break;
    default:                VPANIC("ppIRJumpKind");
    }
}

 void ppIR::ppIRMBusEvent(IRMBusEvent event)
{
    switch (event) {
    case Imbe_Fence:
        vex_printf("Fence"); break;
    case Imbe_CancelReservation:
        vex_printf("CancelReservation"); break;
    default:
        VPANIC("ppIRMBusEvent");
    }
}

 void ppIR::ppIRStmt(const IRStmt* s)
{
    if (!s) {
        vex_printf("!!! IRStmt* which is NULL !!!");
        return;
    }
    switch (s->tag) {
    case Ist_NoOp:
        vex_printf("IR-NoOp");
        break;
    case Ist_IMark:
        vex_printf("------ IMark(0x%llx, %u, %u) ------",
            s->Ist.IMark.addr, s->Ist.IMark.len,
            (UInt)s->Ist.IMark.delta);
        break;
    case Ist_AbiHint:
        vex_printf("====== AbiHint(");
        ppIRExpr(s->Ist.AbiHint.base);
        vex_printf(", %d, ", s->Ist.AbiHint.len);
        ppIRExpr(s->Ist.AbiHint.nia);
        vex_printf(") ======");
        break;
    case Ist_Put:
        vex_printf("PUT(%d) = ", s->Ist.Put.offset);
        ppIRExpr(s->Ist.Put.data);
        break;
    case Ist_PutI:
        ppIRPutI(s->Ist.PutI.details);
        break;
    case Ist_WrTmp:
        ppIRTemp(s->Ist.WrTmp.tmp);
        vex_printf(" = ");
        ppIRExpr(s->Ist.WrTmp.data);
        break;
    case Ist_Store:
        vex_printf("ST%s(", s->Ist.Store.end == Iend_LE ? "le" : "be");
        ppIRExpr(s->Ist.Store.addr);
        vex_printf(") = ");
        ppIRExpr(s->Ist.Store.data);
        break;
    case Ist_StoreG:
        ppIRStoreG(s->Ist.StoreG.details);
        break;
    case Ist_LoadG:
        ppIRLoadG(s->Ist.LoadG.details);
        break;
    case Ist_CAS:
        ppIRCAS(s->Ist.CAS.details);
        break;
    case Ist_LLSC:
        if (s->Ist.LLSC.storedata == NULL) {
            ppIRTemp(s->Ist.LLSC.result);
            vex_printf(" = LD%s-Linked(",
                s->Ist.LLSC.end == Iend_LE ? "le" : "be");
            ppIRExpr(s->Ist.LLSC.addr);
            vex_printf(")");
        }
        else {
            ppIRTemp(s->Ist.LLSC.result);
            vex_printf(" = ( ST%s-Cond(",
                s->Ist.LLSC.end == Iend_LE ? "le" : "be");
            ppIRExpr(s->Ist.LLSC.addr);
            vex_printf(") = ");
            ppIRExpr(s->Ist.LLSC.storedata);
            vex_printf(" )");
        }
        break;
    case Ist_Dirty:
        ppIRDirty(s->Ist.Dirty.details);
        break;
    case Ist_MBE:
        vex_printf("IR-");
        ppIRMBusEvent(s->Ist.MBE.event);
        break;
    case Ist_Exit:
        vex_printf("if (");
        ppIRExpr(s->Ist.Exit.guard);
        vex_printf(") { PUT(%d) = ", s->Ist.Exit.offsIP);
        ppIRConst(s->Ist.Exit.dst);
        vex_printf("; exit-");
        ppIRJumpKind(s->Ist.Exit.jk);
        vex_printf(" } ");
        break;
    default:
        VPANIC("ppIRStmt");
    }
}

 void ppIR::ppIRTypeEnv(const IRTypeEnv* env)
{
    UInt i;
    for (i = 0; i < env->types_used; i++) {
        if (i % 8 == 0)
            vex_printf("   ");
        ppIRTemp(i);
        vex_printf(":");
        ppIRType(env->types[i]);
        if (i % 8 == 7)
            vex_printf("\n");
        else
            vex_printf("   ");
    }
    if (env->types_used > 0 && env->types_used % 8 != 7)
        vex_printf("\n");
}

 void ppIR::ppIRSB(const IRSB* bb)
{
    Int i;
    vex_printf("IRSB {\n");
    ppIRTypeEnv(bb->tyenv);
    vex_printf("\n");
    for (i = 0; i < bb->stmts_used; i++) {
        vex_printf("   ");
        ppIRStmt(bb->stmts[i]);
        vex_printf("\n");
    }
    vex_printf("   PUT(%d) = ", bb->offsIP);
    ppIRExpr(bb->next);
    vex_printf("; exit-");
    ppIRJumpKind(bb->jumpkind);
    vex_printf("\n}\n");
}

 const char* regOff2name(UInt off);
 
 const char* regOff2name(UInt off) {
     class RegOff2Name {
     public:
         const char* AMD64RegNames[AMD64_IR_OFFSET::SS + 8];
         RegOff2Name() {
             memset(AMD64RegNames, 0, sizeof(AMD64RegNames));
             AMD64RegNames[AMD64_IR_OFFSET::RAX] = "RAX";
             AMD64RegNames[AMD64_IR_OFFSET::RCX] = "RCX";
             AMD64RegNames[AMD64_IR_OFFSET::RDX] = "RDX";
             AMD64RegNames[AMD64_IR_OFFSET::RBX] = "RBX";
             AMD64RegNames[AMD64_IR_OFFSET::RSP] = "RSP";
             AMD64RegNames[AMD64_IR_OFFSET::RBP] = "RBP";
             AMD64RegNames[AMD64_IR_OFFSET::RSI] = "RSI";
             AMD64RegNames[AMD64_IR_OFFSET::RDI] = "RDI";
             AMD64RegNames[AMD64_IR_OFFSET::R8] = "R8";
             AMD64RegNames[AMD64_IR_OFFSET::R9] = "R9";
             AMD64RegNames[AMD64_IR_OFFSET::R10] = "R10";
             AMD64RegNames[AMD64_IR_OFFSET::R11] = "R11";
             AMD64RegNames[AMD64_IR_OFFSET::R12] = "R12";
             AMD64RegNames[AMD64_IR_OFFSET::R13] = "R13";
             AMD64RegNames[AMD64_IR_OFFSET::R14] = "R14";
             AMD64RegNames[AMD64_IR_OFFSET::R15] = "R15";
             AMD64RegNames[AMD64_IR_OFFSET::CC_OP] = "CC_OP";
             AMD64RegNames[AMD64_IR_OFFSET::CC_DEP1] = "CC_DEP1";
             AMD64RegNames[AMD64_IR_OFFSET::CC_DEP2] = "CC_DEP2";
             AMD64RegNames[AMD64_IR_OFFSET::CC_NDEP] = "CC_NDEP";
             AMD64RegNames[AMD64_IR_OFFSET::DFLAG] = "DFLAG";
             AMD64RegNames[AMD64_IR_OFFSET::RIP] = "RIP";
             AMD64RegNames[AMD64_IR_OFFSET::ACFLAG] = "ACFLAG";
             AMD64RegNames[AMD64_IR_OFFSET::IDFLAG] = "IDFLAG";
             AMD64RegNames[AMD64_IR_OFFSET::FS_CONST] = "FS_CONST";
             AMD64RegNames[AMD64_IR_OFFSET::SSEROUND] = "SSEROUND";
             AMD64RegNames[AMD64_IR_OFFSET::YMM0] = "YMM0";
             AMD64RegNames[AMD64_IR_OFFSET::YMM1] = "YMM1";
             AMD64RegNames[AMD64_IR_OFFSET::YMM2] = "YMM2";
             AMD64RegNames[AMD64_IR_OFFSET::YMM3] = "YMM3";
             AMD64RegNames[AMD64_IR_OFFSET::YMM4] = "YMM4";
             AMD64RegNames[AMD64_IR_OFFSET::YMM5] = "YMM5";
             AMD64RegNames[AMD64_IR_OFFSET::YMM6] = "YMM6";
             AMD64RegNames[AMD64_IR_OFFSET::YMM7] = "YMM7";
             AMD64RegNames[AMD64_IR_OFFSET::YMM8] = "YMM8";
             AMD64RegNames[AMD64_IR_OFFSET::YMM9] = "YMM9";
             AMD64RegNames[AMD64_IR_OFFSET::YMM10] = "YMM10";
             AMD64RegNames[AMD64_IR_OFFSET::YMM11] = "YMM11";
             AMD64RegNames[AMD64_IR_OFFSET::YMM12] = "YMM12";
             AMD64RegNames[AMD64_IR_OFFSET::YMM13] = "YMM13";
             AMD64RegNames[AMD64_IR_OFFSET::YMM14] = "YMM14";
             AMD64RegNames[AMD64_IR_OFFSET::YMM15] = "YMM15";
             AMD64RegNames[AMD64_IR_OFFSET::YMM16] = "YMM16";
             AMD64RegNames[AMD64_IR_OFFSET::FTOP] = "FTOP";
             AMD64RegNames[AMD64_IR_OFFSET::FPREG] = "FPREG";
             AMD64RegNames[AMD64_IR_OFFSET::FPTAG] = "FPTAG";
             AMD64RegNames[AMD64_IR_OFFSET::FPROUND] = "FPROUND";
             AMD64RegNames[AMD64_IR_OFFSET::FC3210] = "FC3210";
             AMD64RegNames[AMD64_IR_OFFSET::EMNOTE] = "EMNOTE";
             AMD64RegNames[AMD64_IR_OFFSET::CMSTART] = "CMSTART";
             AMD64RegNames[AMD64_IR_OFFSET::CMLEN] = "CMLEN";
             AMD64RegNames[AMD64_IR_OFFSET::NRADDR] = "NRADDR";
             AMD64RegNames[AMD64_IR_OFFSET::SC_CLASS] = "SC_CLASS";
             AMD64RegNames[AMD64_IR_OFFSET::GS_CONST] = "GS_CONST";
             AMD64RegNames[AMD64_IR_OFFSET::IP_AT_SYSCALL] = "IP_AT_SYSCALL";
             AMD64RegNames[AMD64_IR_OFFSET::LDT] = "LDT";
             AMD64RegNames[AMD64_IR_OFFSET::GDT] = "GDT";
             AMD64RegNames[AMD64_IR_OFFSET::CS] = "CS";
             AMD64RegNames[AMD64_IR_OFFSET::DS] = "DS";
             AMD64RegNames[AMD64_IR_OFFSET::ES] = "ES";
             AMD64RegNames[AMD64_IR_OFFSET::FS] = "FS";
             AMD64RegNames[AMD64_IR_OFFSET::GS] = "GS";
             AMD64RegNames[AMD64_IR_OFFSET::SS] = "SS";
         }
     };
     static RegOff2Name Reg;
     for (int curr = off; curr; curr--) {
         const char* R = Reg.AMD64RegNames[curr];
         if (R) return R;
     }
     assert(0 && "error offset");
 };

