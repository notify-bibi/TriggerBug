
#include "X86/x86CCall.h"
extern "C" {
    #include "guest_x86_defs.h"
    UInt vex_printf(const HChar* format, ...);
    __attribute__((noreturn))  void vpanic(const HChar* str);
}

#define CC_DEP1 cc_dep1_formal
#define CC_DEP2 cc_dep2_formal
#define CC_NDEP cc_ndep_formal

#define PREAMBLE(__data_bits)                                   \
   /* const */ UInt DATA_MASK                                   \
      = __data_bits==8 ? 0xFF                                   \
                       : (__data_bits==16 ? 0xFFFF              \
                                          : 0xFFFFFFFF);        \
   /* const */ UInt SIGN_MASK = 1u << (__data_bits - 1);        \


/*-------------------------------------------------------------*/

#define ACTIONS_COPY(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof) \
{                                                               \
   MASKcf(return bit2ret(CC_DEP1, X86G_CC_SHIFT_C);           )\
   MASKpf(return bit2ret(CC_DEP1, X86G_CC_SHIFT_P);           )\
   MASKaf(return bit2ret(CC_DEP1, X86G_CC_SHIFT_A);           )\
   MASKzf(return bit2ret(CC_DEP1, X86G_CC_SHIFT_Z);           )\
   MASKsf(return bit2ret(CC_DEP1, X86G_CC_SHIFT_S);           )\
   MASKof(return bit2ret(CC_DEP1, X86G_CC_SHIFT_O);           )\
}


/*-------------------------------------------------------------*/

#define ACTIONS_ADD(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                                                 \
{                                                                                                                                   \
   PREAMBLE(DATA_BITS);                                                                                                             \
   {                                                                                                                                \
     /*ok*/MASKcf(return DATA_UTYPE((CC_DEP1 + CC_DEP2)) < DATA_UTYPE(CC_DEP1);                                                     )\
     /*ok*/MASKpf(return parity_table((CC_DEP1 + CC_DEP2));                                                                         )\
     /*ok*/MASKaf(return bit2ret((CC_DEP1 + CC_DEP2) ^ CC_DEP1 ^ CC_DEP2, X86G_CC_SHIFT_A);                                       )\
     /*ok*/MASKzf(return (DATA_UTYPE((CC_DEP1 + CC_DEP2)) == 0) ;                                                                )\
     /*ok*/MASKsf(return bit2ret((CC_DEP1 + CC_DEP2), DATA_BITS - 1) ;                                                              )\
     /*ok*/MASKof(return bit2ret((CC_DEP1 ^ CC_DEP2 ^ -1) & (CC_DEP1 ^ (CC_DEP1 + CC_DEP2)),  DATA_BITS - 1) ;                   )\
   }                                                                                                                                \
}

/*-------------------------------------------------------------*/

#define ACTIONS_SUB(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                                                 \
{                                                                                                                                   \
   PREAMBLE(DATA_BITS);                                                                                                             \
   {                                                                                                                                \
     /*ok*/MASKcf(return DATA_UTYPE(CC_DEP1) < DATA_UTYPE(CC_DEP2);                                                                 )\
     /*ok*/MASKpf(return parity_table((CC_DEP1 - CC_DEP2));                                                                         )\
     /*ok*/MASKaf(return bit2ret((CC_DEP1 - CC_DEP2) ^ CC_DEP1 ^ CC_DEP2, X86G_CC_SHIFT_A);                                       )\
     /*ok*/MASKzf(return (DATA_UTYPE((CC_DEP1 - CC_DEP2)) == 0u) ;                                                                )\
     /*ok*/MASKsf(return bit2ret((CC_DEP1 - CC_DEP2), DATA_BITS - 1);                                                               )\
     /*ok*/MASKof(return bit2ret((CC_DEP1 ^ CC_DEP2) & (CC_DEP1 ^ (CC_DEP1 - CC_DEP2)), DATA_BITS - 1) ;                            )\
   }                                                                                                                                \
}

/*-------------------------------------------------------------*/

#define ACTIONS_ADC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                                                 \
{                                                                                                                                   \
   PREAMBLE(DATA_BITS);                                                                                                             \
   {                                                                                                                                \
     auto oldC = CC_NDEP & X86G_CC_MASK_C;                                                                                        \
     /*ok*/MASKcf(return ite(oldC!=0,DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)) <= DATA_UTYPE(CC_DEP1),DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)) < DATA_UTYPE(CC_DEP1))  ;)\
     /*ok*/MASKpf(return parity_table(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC));                                                       )\
     /*ok*/MASKaf(return bit2ret((((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC) ^ CC_DEP1 ^ (CC_DEP2 ^ oldC)), X86G_CC_SHIFT_A);          )\
     /*ok*/MASKzf(return (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)) == 0) ;                                              )\
     /*ok*/MASKsf(return bit2ret(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC),  DATA_BITS - 1);                                            )\
     /*ok*/MASKof(return bit2ret((CC_DEP1 ^ (CC_DEP2 ^ oldC) ^ -1) & (CC_DEP1 ^ ((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)), DATA_BITS - 1) ;                                                                             )\
   }                                                                                                                                \
}

/*-------------------------------------------------------------*/

#define ACTIONS_SBB(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                                                                 \
{                                                                                                                                                   \
   PREAMBLE(DATA_BITS);                                                                                                                             \
   {                                                                                                                                                \
     auto oldC = CC_NDEP & X86G_CC_MASK_C;                                                                                                        \
     /*ok*/MASKcf(return  ite(oldC!=0, DATA_UTYPE(CC_DEP1) <= DATA_UTYPE((CC_DEP2 ^ oldC)),DATA_UTYPE(CC_DEP1) < DATA_UTYPE((CC_DEP2 ^ oldC)));  )\
     /*ok*/MASKpf(return parity_table(((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC));                                                                       )\
     /*ok*/MASKaf(return bit2ret((((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC) ^ CC_DEP1 ^ (CC_DEP2 ^ oldC)), X86G_CC_SHIFT_A);                          )\
     /*ok*/MASKzf(return (DATA_UTYPE(((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC)) == 0) ;                                                              )\
     /*ok*/MASKsf(return bit2ret(((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC),  DATA_BITS - 1);                                                            )\
     /*ok*/MASKof(return bit2ret((CC_DEP1 ^ (CC_DEP2 ^ oldC)) & (CC_DEP1 ^ ((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC)), DATA_BITS - 1) ;                 )\
   }                                                                                                                                                \
}

/*-------------------------------------------------------------*/

#define ACTIONS_LOGIC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                       \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKpf(return parity_table(CC_DEP1);                                                             )\
     /*ok*/MASKaf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1,  DATA_BITS - 1);                                                  )\
     /*ok*/MASKof(return rsval<bool>((CC_DEP1), false);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_INC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                         \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return bit2ret(CC_NDEP,X86G_CC_SHIFT_C);                                                )\
     /*ok*/MASKpf(return parity_table(CC_DEP1);                                                             )\
     /*ok*/MASKaf(return bit2ret((CC_DEP1 ^ (CC_DEP1 - 1) ^ 1), X86G_CC_SHIFT_A);                   )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return ((CC_DEP1 & DATA_MASK) == SIGN_MASK) ;                                             )\
                                                                                                            \
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_DEC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                         \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return bit2ret(CC_NDEP,X86G_CC_SHIFT_C);                                                )\
     /*ok*/MASKpf(return parity_table(CC_DEP1);                                                             )\
     /*ok*/MASKaf(return bit2ret((CC_DEP1 ^ (CC_DEP1 + 1) ^ 1), X86G_CC_SHIFT_A);                   )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return ((CC_DEP1 & DATA_MASK) == ((UInt)SIGN_MASK - 1)) ;                                )\
                                                                                                            \
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_SHL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                         \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return bit2ret(CC_DEP2 , (DATA_BITS - 1));                                                )\
     /*ok*/MASKpf(return parity_table(CC_DEP1);                                                             )\
     /*ok*/MASKaf(return rsval<bool>((CC_DEP1), false); /* undefined */                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /* of is defined if shift count == 1 */                                                                \
     /*ok*/MASKof(return bit2ret(CC_DEP2 ^ CC_DEP1, DATA_BITS - 1);)                                        \
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_SHR(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                         \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return bit2ret(CC_DEP2, X86G_CC_SHIFT_C);                                               )\
     /*ok*/MASKpf(return parity_table(CC_DEP1);                                                             )\
     /*ok*/MASKaf(return rsval<bool>((CC_DEP1), false); /* undefined */                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /* of is defined if shift count == 1 */                                                                \
     /*ok*/MASKof(return bit2ret(CC_DEP2 ^ CC_DEP1, DATA_BITS - 1);)                                        \
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

/* ROL: cf' = lsb(result).  of' = msb(result) ^ lsb(result). */
/* DEP1 = result, NDEP = old flags */
#define ACTIONS_ROL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                         \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
    /*ok*/MASKcf(  return bit2ret(CC_DEP1, X86G_CC_SHIFT_C);                                              )\
    /*ok*/MASKpf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_P);                                              )\
    /*ok*/MASKaf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_A);                                              )\
    /*ok*/MASKzf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_Z);                                              )\
    /*ok*/MASKsf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_S);                                              )\
    /*ok*/MASKof(  return bit2ret(CC_DEP1, DATA_BITS - 1)^(bit2ret(CC_DEP1, 0));                     )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

/* ROR: cf' = msb(result).  of' = msb(result) ^ msb-1(result). */
/* DEP1 = result, NDEP = old flags */
#define ACTIONS_ROR(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                         \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
    /*ok*/MASKcf(  return bit2ret(CC_DEP1, (DATA_BITS-1));                                                  )\
    /*ok*/MASKpf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_P);                                              )\
    /*ok*/MASKaf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_A);                                              )\
    /*ok*/MASKzf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_Z);                                              )\
    /*ok*/MASKsf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_S);                                              )\
    /*ok*/MASKof(  return bit2ret(CC_DEP1, DATA_BITS - 1)^(bit2ret(CC_DEP1, DATA_BITS - 2));         )\
   }                                                                                                        \
}


/*-------------------------------------------------------------*/

#define ACTIONS_ANDN(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                        \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKpf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKaf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return rsval<bool>((CC_DEP1), false);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_BLSI(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                        \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return (DATA_UTYPE(CC_DEP2) != 0);                                                     )\
     /*ok*/MASKpf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKaf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return rsval<bool>((CC_DEP1), false);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_BLSMSK(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                      \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return (DATA_UTYPE(CC_DEP2) == 0);                                                     )\
     /*ok*/MASKpf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKaf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKzf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return rsval<bool>((CC_DEP1), false);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_BLSR(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                        \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return (DATA_UTYPE(CC_DEP2) == 0);                                                     )\
     /*ok*/MASKpf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKaf(return rsval<bool>((CC_DEP1), false);                                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return rsval<bool>((CC_DEP1), false);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_ADCX(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                        \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
    /*ok*/MASKcf({ auto oldOC = (CC_NDEP >> X86G_CC_SHIFT_C) & 1;                                      \
                   return ite(oldOC==1,                                                                  \
        (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) <= DATA_UTYPE(CC_DEP1)),                       \
        (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) < DATA_UTYPE(CC_DEP1)));    }                  )\
    /*ok*/MASKpf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_P);                                              )\
    /*ok*/MASKaf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_A);                                              )\
    /*ok*/MASKzf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_Z);                                              )\
    /*ok*/MASKsf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_S);                                              )\
    /*ok*/MASKof(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_O);                                              )\
   }                                                                                                        \
}

#define ACTIONS_ADOX(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE,FLAGNAME)               \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
    /*ok*/MASKpf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_P);                                              )\
    /*ok*/MASKaf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_A);                                              )\
    /*ok*/MASKzf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_Z);                                              )\
    /*ok*/MASKsf(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_S);                                              )\
    /*ok*/MASKof(  return bit2ret(CC_NDEP, X86G_CC_SHIFT_O);                                              )\
        auto oldOC = (CC_NDEP >> X86G_CC_SHIFT_O) & 1;                                                 \
    /*ok*/MASKof(  return ite(oldOC==1,                                                                  \
        (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) <= DATA_UTYPE(CC_DEP1)),                       \
        (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) < DATA_UTYPE(CC_DEP1)));                       )\
   }                                                                                                        \
}


/*-------------------------------------------------------------*/

#define ACTIONS_UMUL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE, NARROWtoU,DATA_U2TYPE,NARROWto2U)           \
{                                                                                                                               \
   PREAMBLE(DATA_BITS);                                                                                                         \
   {                                                                                                                            \
     auto u2m = CC_DEP1.extract<(sizeof(DATA_UTYPE) << 3) - 1, 0>().zext<false, ((sizeof(DATA_U2TYPE) - sizeof(DATA_UTYPE)) << 3)>()*      \
                CC_DEP2.extract<(sizeof(DATA_UTYPE) << 3) - 1, 0>().zext<false, ((sizeof(DATA_U2TYPE) - sizeof(DATA_UTYPE)) << 3)>();      \
     /*ok*/MASKcf(return u2m.extract<(sizeof(DATA_U2TYPE) << 3) - 1, DATA_BITS>() != (DATA_UTYPE)0;                               )\
     /*ok*/MASKpf(return parity_table(u2m);                                                                                     )\
     /*ok*/MASKaf(return rsval<bool>((CC_DEP1), false); /* undefined */                                                                  )\
     /*ok*/MASKzf(return (u2m.extract<DATA_BITS - 1, 0>() == (DATA_UTYPE)0);                                                      )\
     /*ok*/MASKsf(return bit2ret(u2m, DATA_BITS - 1);                                                                           )\
     /*ok*/MASKof(return u2m.extract<(sizeof(DATA_U2TYPE) << 3) - 1, DATA_BITS>() != (DATA_UTYPE)0;                               )\
   }								                                                                                            \
}

/*-------------------------------------------------------------*/

#define ACTIONS_SMUL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_STYPE,NARROWtoS,DATA_S2TYPE,NARROWto2S)           \
{                                                                                                                               \
   PREAMBLE(DATA_BITS);                                                                                                         \
   {                                                                                                                            \
     auto u2m = CC_DEP1.extract<(sizeof(DATA_STYPE) << 3) - 1, 0>().sext<true, ((sizeof(DATA_S2TYPE) - sizeof(DATA_STYPE)) << 3)>()*      \
                CC_DEP2.extract<(sizeof(DATA_STYPE) << 3) - 1, 0>().sext<true, ((sizeof(DATA_S2TYPE) - sizeof(DATA_STYPE)) << 3)>();      \
     /*ok*/MASKcf(return u2m.extract<(sizeof(DATA_S2TYPE) << 3) - 1, DATA_BITS>() != (u2m.extract<DATA_BITS - 1, 0>().to_signed<true>()>>(DATA_BITS-1));)\
     /*ok*/MASKpf(return parity_table(u2m);                                                                                     )\
     /*ok*/MASKaf(return rsval<bool>((CC_DEP1), false); /* undefined */                                                                  )\
     /*ok*/MASKzf(return (u2m.extract<DATA_BITS - 1, 0>() == (DATA_STYPE)0);                                                      )\
     /*ok*/MASKsf(return bit2ret(u2m, DATA_BITS - 1);                                                                           )\
     /*ok*/MASKof(return u2m.extract<(sizeof(DATA_S2TYPE) << 3) - 1, DATA_BITS>() != (u2m.extract<DATA_BITS - 1, 0>().to_signed<true>()>>(DATA_BITS-1));)\
   }								                                                                                            \
}

/*-------------------------------------------------------------*/


#define ACTIONS_COPY_cf()       ACTIONS_COPY    (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_COPY_pf()       ACTIONS_COPY    (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_COPY_af()       ACTIONS_COPY    (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_COPY_zf()       ACTIONS_COPY    (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_COPY_sf()       ACTIONS_COPY    (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO)
#define ACTIONS_COPY_of()       ACTIONS_COPY    (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO)
#define ACTIONS_ADD_cf(A, B)    ACTIONS_ADD     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_pf(A, B)    ACTIONS_ADD     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_af(A, B)    ACTIONS_ADD     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_zf(A, B)    ACTIONS_ADD     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_sf(A, B)    ACTIONS_ADD     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_of(A, B)    ACTIONS_ADD     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ADC_cf(A, B)    ACTIONS_ADC     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_pf(A, B)    ACTIONS_ADC     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_af(A, B)    ACTIONS_ADC     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_zf(A, B)    ACTIONS_ADC     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_sf(A, B)    ACTIONS_ADC     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_of(A, B)    ACTIONS_ADC     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_SUB_cf(A, B)    ACTIONS_SUB     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_pf(A, B)    ACTIONS_SUB     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_af(A, B)    ACTIONS_SUB     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_zf(A, B)    ACTIONS_SUB     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_sf(A, B)    ACTIONS_SUB     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_of(A, B)    ACTIONS_SUB     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_SBB_cf(A, B)    ACTIONS_SBB     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_pf(A, B)    ACTIONS_SBB     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_af(A, B)    ACTIONS_SBB     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_zf(A, B)    ACTIONS_SBB     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_sf(A, B)    ACTIONS_SBB     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_of(A, B)    ACTIONS_SBB     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_LOGIC_cf(A, B)  ACTIONS_LOGIC   (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_pf(A, B)  ACTIONS_LOGIC   (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_af(A, B)  ACTIONS_LOGIC   (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_zf(A, B)  ACTIONS_LOGIC   (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_sf(A, B)  ACTIONS_LOGIC   (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_of(A, B)  ACTIONS_LOGIC   (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_INC_cf(A, B)    ACTIONS_INC     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_pf(A, B)    ACTIONS_INC     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_af(A, B)    ACTIONS_INC     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_zf(A, B)    ACTIONS_INC     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_sf(A, B)    ACTIONS_INC     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_of(A, B)    ACTIONS_INC     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_DEC_cf(A, B)    ACTIONS_DEC     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_pf(A, B)    ACTIONS_DEC     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_af(A, B)    ACTIONS_DEC     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_zf(A, B)    ACTIONS_DEC     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_sf(A, B)    ACTIONS_DEC     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_of(A, B)    ACTIONS_DEC     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_SHL_cf(A, B)    ACTIONS_SHL     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_pf(A, B)    ACTIONS_SHL     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_af(A, B)    ACTIONS_SHL     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_zf(A, B)    ACTIONS_SHL     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_sf(A, B)    ACTIONS_SHL     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_of(A, B)    ACTIONS_SHL     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_SHR_cf(A, B)    ACTIONS_SHR     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_pf(A, B)    ACTIONS_SHR     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_af(A, B)    ACTIONS_SHR     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_zf(A, B)    ACTIONS_SHR     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_sf(A, B)    ACTIONS_SHR     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_of(A, B)    ACTIONS_SHR     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ROL_cf(A, B)    ACTIONS_ROL     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_pf(A, B)    ACTIONS_ROL     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_af(A, B)    ACTIONS_ROL     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_zf(A, B)    ACTIONS_ROL     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_sf(A, B)    ACTIONS_ROL     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_of(A, B)    ACTIONS_ROL     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ROR_cf(A, B)    ACTIONS_ROR     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_pf(A, B)    ACTIONS_ROR     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_af(A, B)    ACTIONS_ROR     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_zf(A, B)    ACTIONS_ROR     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_sf(A, B)    ACTIONS_ROR     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_of(A, B)    ACTIONS_ROR     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ANDN_cf(A, B)   ACTIONS_ANDN    (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_pf(A, B)   ACTIONS_ANDN    (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_af(A, B)   ACTIONS_ANDN    (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_zf(A, B)   ACTIONS_ANDN    (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_sf(A, B)   ACTIONS_ANDN    (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_of(A, B)   ACTIONS_ANDN    (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_BLSI_cf(A, B)   ACTIONS_BLSI    (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_pf(A, B)   ACTIONS_BLSI    (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_af(A, B)   ACTIONS_BLSI    (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_zf(A, B)   ACTIONS_BLSI    (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_sf(A, B)   ACTIONS_BLSI    (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_of(A, B)   ACTIONS_BLSI    (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_BLSMSK_cf(A, B) ACTIONS_BLSMSK  (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_pf(A, B) ACTIONS_BLSMSK  (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_af(A, B) ACTIONS_BLSMSK  (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_zf(A, B) ACTIONS_BLSMSK  (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_sf(A, B) ACTIONS_BLSMSK  (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_of(A, B) ACTIONS_BLSMSK  (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_BLSR_cf(A, B)   ACTIONS_BLSR    (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_pf(A, B)   ACTIONS_BLSR    (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_af(A, B)   ACTIONS_BLSR    (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_zf(A, B)   ACTIONS_BLSR    (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_sf(A, B)   ACTIONS_BLSR    (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_of(A, B)   ACTIONS_BLSR    (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ADCX_cf(A, B)   ACTIONS_ADCX     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADCX_pf(A, B)   ACTIONS_ADCX     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADCX_af(A, B)   ACTIONS_ADCX     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADCX_zf(A, B)   ACTIONS_ADCX     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADCX_sf(A, B)   ACTIONS_ADCX     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ADCX_of(A, B)   ACTIONS_ADCX     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ADOX_cf(A, B)   ACTIONS_ADOX     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADOX_pf(A, B)   ACTIONS_ADOX     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADOX_af(A, B)   ACTIONS_ADOX     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADOX_zf(A, B)   ACTIONS_ADOX     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADOX_sf(A, B)   ACTIONS_ADOX     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ADOX_of(A, B)   ACTIONS_ADOX     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_UMUL_cf(A, B, C, D, E) ACTIONS_UMUL(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_UMUL_pf(A, B, C, D, E) ACTIONS_UMUL(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_UMUL_af(A, B, C, D, E) ACTIONS_UMUL(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_UMUL_zf(A, B, C, D, E) ACTIONS_UMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_UMUL_sf(A, B, C, D, E) ACTIONS_UMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_UMUL_of(A, B, C, D, E) ACTIONS_UMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B, C, D, E)
#define ACTIONS_SMUL_cf(A, B, C, D, E) ACTIONS_SMUL(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_SMUL_pf(A, B, C, D, E) ACTIONS_SMUL(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_SMUL_af(A, B, C, D, E) ACTIONS_SMUL(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_SMUL_zf(A, B, C, D, E) ACTIONS_SMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_SMUL_sf(A, B, C, D, E) ACTIONS_SMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B, C, D, E)
#define ACTIONS_SMUL_of(A, B, C, D, E) ACTIONS_SMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B, C, D, E)



/* CALLED FROM GENERATED CODE: CLEAN HELPER */
/* Calculate all the 6 flags from the supplied thunk parameters.
   Worker function, not directly called from generated code. */

#define z3_x86g_calculate_eflags_(FLAG)                                             \
 rsbool z3_x86g_calculate_eflags_##FLAG (                        \
UInt cc_op,                                                      \
const rsval<uint32_t> &cc_dep1_formal,                           \
const rsval<uint32_t> &cc_dep2_formal,                           \
const rsval<uint32_t> &cc_ndep_formal )                          \
{                                                                                   \
   switch (cc_op) {                                                                 \
      case X86G_CC_OP_COPY:   ACTIONS_COPY_##FLAG()                                 \
                                                                                    \
      case X86G_CC_OP_ADDB:   ACTIONS_ADD_##FLAG( 8,  UChar_extract  );             \
      case X86G_CC_OP_ADDW:   ACTIONS_ADD_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_ADDL:   ACTIONS_ADD_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_ADCB:   ACTIONS_ADC_##FLAG( 8,  UChar_extract  );             \
      case X86G_CC_OP_ADCW:   ACTIONS_ADC_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_ADCL:   ACTIONS_ADC_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_SUBB:   ACTIONS_SUB_##FLAG(  8, UChar_extract  );             \
      case X86G_CC_OP_SUBW:   ACTIONS_SUB_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_SUBL:   ACTIONS_SUB_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_SBBB:   ACTIONS_SBB_##FLAG(  8, UChar_extract  );             \
      case X86G_CC_OP_SBBW:   ACTIONS_SBB_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_SBBL:   ACTIONS_SBB_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_LOGICB: ACTIONS_LOGIC_##FLAG(  8, UChar_extract  );           \
      case X86G_CC_OP_LOGICW: ACTIONS_LOGIC_##FLAG( 16, UShort_extract );           \
      case X86G_CC_OP_LOGICL: ACTIONS_LOGIC_##FLAG( 32, UInt_extract   );           \
                                                                                    \
      case X86G_CC_OP_INCB:   ACTIONS_INC_##FLAG(  8, UChar_extract  );             \
      case X86G_CC_OP_INCW:   ACTIONS_INC_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_INCL:   ACTIONS_INC_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_DECB:   ACTIONS_DEC_##FLAG(  8, UChar_extract  );             \
      case X86G_CC_OP_DECW:   ACTIONS_DEC_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_DECL:   ACTIONS_DEC_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_SHLB:   ACTIONS_SHL_##FLAG(  8, UChar_extract  );             \
      case X86G_CC_OP_SHLW:   ACTIONS_SHL_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_SHLL:   ACTIONS_SHL_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_SHRB:   ACTIONS_SHR_##FLAG(  8, UChar_extract  );             \
      case X86G_CC_OP_SHRW:   ACTIONS_SHR_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_SHRL:   ACTIONS_SHR_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_ROLB:   ACTIONS_ROL_##FLAG(  8, UChar_extract  );             \
      case X86G_CC_OP_ROLW:   ACTIONS_ROL_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_ROLL:   ACTIONS_ROL_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_RORB:   ACTIONS_ROR_##FLAG(  8, UChar_extract  );             \
      case X86G_CC_OP_RORW:   ACTIONS_ROR_##FLAG( 16, UShort_extract );             \
      case X86G_CC_OP_RORL:   ACTIONS_ROR_##FLAG( 32, UInt_extract   );             \
                                                                                    \
      case X86G_CC_OP_UMULB:  ACTIONS_UMUL_##FLAG(  8, UChar,  toUChar,             \
                                                UShort, toUShort );                 \
      case X86G_CC_OP_UMULW:  ACTIONS_UMUL_##FLAG( 16, UShort, toUShort,            \
                                                UInt,   toUInt );                   \
      case X86G_CC_OP_UMULL:  ACTIONS_UMUL_##FLAG( 32, UInt,   toUInt,              \
                                                ULong,  idULong );                  \
                                                                                    \
      case X86G_CC_OP_SMULB:  ACTIONS_SMUL_##FLAG(  8, Char,   toUChar,             \
                                                Short,  toUShort );                 \
      case X86G_CC_OP_SMULW:  ACTIONS_SMUL_##FLAG( 16, Short,  toUShort,            \
                                                Int,    toUInt   );                 \
      case X86G_CC_OP_SMULL:  ACTIONS_SMUL_##FLAG( 32, Int,    toUInt,              \
                                                Long,   idULong );                  \
                                                                                    \
      default:                                                                      \
         /* shouldn't really make these calls from generated code */                \
         vex_printf("x86g_calculate_eflags_all_WRK(X86)");                          \
         std::cout << std::hex<< cc_op << ", " << cc_dep1_formal << ", " << cc_dep2_formal << ", " << cc_ndep_formal << std::endl; \
         vpanic("x86g_calculate_eflags_all_WRK(X86)");                              \
   }                                                                                \
}


z3_x86g_calculate_eflags_(cf);
z3_x86g_calculate_eflags_(pf);
z3_x86g_calculate_eflags_(af);
z3_x86g_calculate_eflags_(zf);
z3_x86g_calculate_eflags_(sf);
z3_x86g_calculate_eflags_(of);






/* CALLED FROM GENERATED CODE: CLEAN HELPER */
/* returns 1 or 0 */
inline static rsbool _z3_x86g_calculate_condition (  
    Int/*X86Condcode*/ cond,
    Int cc_op,
    const rsval<uint32_t>& cc_dep1, 
    const rsval<uint32_t>& cc_dep2,
    const rsval<uint32_t>& cc_ndep )
{
   
   switch (cond) {
      case X86CondNO:
      case X86CondO: /* OF == 1 */
         return z3_x86g_calculate_eflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep);

      case X86CondNZ:
      case X86CondZ: /* ZF == 1 */
         return z3_x86g_calculate_eflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep);

      case X86CondNB:
      case X86CondB: /* CF == 1 */
         return z3_x86g_calculate_eflags_cf(cc_op, cc_dep1, cc_dep2, cc_ndep);

      case X86CondNBE:
      case X86CondBE: /* (CF or ZF) == 1 */
         return z3_x86g_calculate_eflags_cf(cc_op, cc_dep1, cc_dep2, cc_ndep) || z3_x86g_calculate_eflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep);
         

      case X86CondNS:
      case X86CondS: /* SF == 1 */
         return z3_x86g_calculate_eflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep);

      case X86CondNP:
      case X86CondP: /* PF == 1 */
         return z3_x86g_calculate_eflags_pf(cc_op, cc_dep1, cc_dep2, cc_ndep);

      case X86CondNL:
      case X86CondL: /* (SF xor OF) == 1 */
          return z3_x86g_calculate_eflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep) ^ (z3_x86g_calculate_eflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep));

      case X86CondNLE:
      case X86CondLE: /* ((SF xor OF) or ZF)  == 1 */{
         auto sf = z3_x86g_calculate_eflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep);
         auto of = z3_x86g_calculate_eflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep);
         auto zf = z3_x86g_calculate_eflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep);
         return (sf ^ of) || zf;
      }
      default:
         /* shouldn't really make these calls from generated code */
          vex_printf("x86g_calculate_condition");
          std::cout << std::hex << cond << std::hex << cc_op << ", " << cc_dep1 << ", " << cc_dep2 << ", " << cc_ndep << std::endl;
          vpanic("x86g_calculate_condition");
   }
}


rsval<uint32_t> z3_x86g_calculate_condition(
    const rsval<uint32_t>&/*X86Condcode*/ cond,
    const rsval<uint32_t>& cc_op,
    const rsval<uint32_t>& cc_dep1,
    const rsval<uint32_t>& cc_dep2,
    const rsval<uint32_t>& cc_ndep)
{
    if (cc_op.symb()) {
        vassert(0);
        std::cout <<"cc_op is "<< cc_op.tos().simplify() << std::endl;
        rsval<uint32_t> ret = z3_x86g_calculate_condition(cond.tor(), rcval<uint32_t>(cond.ctx(), 0), cc_dep1, cc_dep2, cc_ndep);
        for (int i = 0; i < 39; i++) {
            rsval<uint32_t> one = z3_x86g_calculate_condition(cond.tor(), rcval<uint32_t>(cond.ctx(), i), cc_dep1, cc_dep2, cc_ndep);
            ret = ite(cc_op == i, one, ret);
        } 
        return ret;
    }
    auto flag = _z3_x86g_calculate_condition(cond.tor(), cc_op.tor(), cc_dep1, cc_dep2, cc_ndep);
    if (((int)cond.tor() & 1)) {
        flag = !flag;
    }
    return flag;
}

rsval<uint32_t> z3_x86g_calculate_eflags_c(
    const rsval<uint32_t>& cc_op,
    const rsval<uint32_t>& cc_dep1,
    const rsval<uint32_t>& cc_dep2,
    const rsval<uint32_t>& cc_ndep)
{
    return z3_x86g_calculate_eflags_cf(cc_op.tor(), cc_dep1, cc_dep2, cc_ndep);
}

rsval<uint32_t> z3_x86g_calculate_eflags_all(
    const rsval<uint32_t>& cc_op,
    const rsval<uint32_t>& cc_dep1,
    const rsval<uint32_t>& cc_dep2,
    const rsval<uint32_t>& cc_ndep) 
{

    auto of = ite(z3_x86g_calculate_eflags_of(cc_op.tor(), cc_dep1, cc_dep2, cc_ndep), rsval<uint32_t>(cc_op, X86G_CC_MASK_O), rsval<uint32_t>(cc_op, 0u));
    auto sf = ite(z3_x86g_calculate_eflags_sf(cc_op.tor(), cc_dep1, cc_dep2, cc_ndep), rsval<uint32_t>(cc_op, X86G_CC_MASK_S), rsval<uint32_t>(cc_op, 0u));
    auto zf = ite(z3_x86g_calculate_eflags_zf(cc_op.tor(), cc_dep1, cc_dep2, cc_ndep), rsval<uint32_t>(cc_op, X86G_CC_MASK_Z), rsval<uint32_t>(cc_op, 0u));
    auto af = ite(z3_x86g_calculate_eflags_af(cc_op.tor(), cc_dep1, cc_dep2, cc_ndep), rsval<uint32_t>(cc_op, X86G_CC_MASK_A), rsval<uint32_t>(cc_op, 0u));
    auto cf = ite(z3_x86g_calculate_eflags_cf(cc_op.tor(), cc_dep1, cc_dep2, cc_ndep), rsval<uint32_t>(cc_op, X86G_CC_MASK_C), rsval<uint32_t>(cc_op, 0u));
    auto pf = ite(z3_x86g_calculate_eflags_pf(cc_op.tor(), cc_dep1, cc_dep2, cc_ndep), rsval<uint32_t>(cc_op, X86G_CC_MASK_P), rsval<uint32_t>(cc_op, 0u));
    return of | sf | zf | af | cf | pf;
}

