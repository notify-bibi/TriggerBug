extern "C" {
#include "guest_amd64_defs.h"
}


#define CC_DEP1 cc_dep1_formal
#define CC_DEP2 cc_dep2_formal
#define CC_NDEP cc_ndep_formal


#define PREAMBLE(__data_bits)                                   \
   /* const */ ULong DATA_MASK                                  \
      = __data_bits==8                                          \
           ? 0xFFULL                                            \
           : (__data_bits==16                                   \
                ? 0xFFFFULL                                     \
                : (__data_bits==32                              \
                     ? 0xFFFFFFFFULL                            \
                     : 0xFFFFFFFFFFFFFFFFULL));                 \
   /* const */ ULong SIGN_MASK = 1ULL << (__data_bits - 1);     \


/*-------------------------------------------------------------*/

#define ACTIONS_COPY(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof) \
{                                                               \
   MASKcf(return bit2ret(CC_DEP1, AMD64G_CC_SHIFT_C);           )\
   MASKpf(return bit2ret(CC_DEP1, AMD64G_CC_SHIFT_P);           )\
   MASKaf(return bit2ret(CC_DEP1, AMD64G_CC_SHIFT_A);           )\
   MASKzf(return bit2ret(CC_DEP1, AMD64G_CC_SHIFT_Z);           )\
   MASKsf(return bit2ret(CC_DEP1, AMD64G_CC_SHIFT_S);           )\
   MASKof(return bit2ret(CC_DEP1, AMD64G_CC_SHIFT_O);           )\
}


/*-------------------------------------------------------------*/

#define ACTIONS_ADD(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                                                 \
{                                                                                                                                   \
   PREAMBLE(DATA_BITS);                                                                                                             \
   {                                                                                                                                \
     /*ok*/MASKcf(return DATA_UTYPE((CC_DEP1 + CC_DEP2)) < DATA_UTYPE(CC_DEP1);                                                     )\
     /*ok*/MASKpf(return parity_table((CC_DEP1 + CC_DEP2));                                                                         )\
     /*ok*/MASKaf(return bit2ret((CC_DEP1 + CC_DEP2) ^ CC_DEP1 ^ CC_DEP2, AMD64G_CC_SHIFT_A);                                       )\
     /*ok*/MASKzf(return (DATA_UTYPE((CC_DEP1 + CC_DEP2)) == 0ull) ;                                                                )\
     /*ok*/MASKsf(return bit2ret((CC_DEP1 + CC_DEP2), DATA_BITS - 1) ;                                                              )\
     /*ok*/MASKof(return bit2ret((CC_DEP1 ^ CC_DEP2 ^ -1ull) & (CC_DEP1 ^ (CC_DEP1 + CC_DEP2)),  DATA_BITS - 1) ;                   )\
   }                                                                                                                                \
}

/*-------------------------------------------------------------*/

#define ACTIONS_SUB(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                                                 \
{                                                                                                                                   \
   PREAMBLE(DATA_BITS);                                                                                                             \
   {                                                                                                                                \
     /*ok*/MASKcf(return DATA_UTYPE(CC_DEP1) < DATA_UTYPE(CC_DEP2);                                                                 )\
     /*ok*/MASKpf(return parity_table((CC_DEP1 - CC_DEP2));                                                                         )\
     /*ok*/MASKaf(return bit2ret((CC_DEP1 - CC_DEP2) ^ CC_DEP1 ^ CC_DEP2, AMD64G_CC_SHIFT_A);                                       )\
     /*ok*/MASKzf(return (DATA_UTYPE((CC_DEP1 - CC_DEP2)) == 0ull) ;                                                                )\
     /*ok*/MASKsf(return bit2ret((CC_DEP1 - CC_DEP2), DATA_BITS - 1);                                                               )\
     /*ok*/MASKof(return bit2ret((CC_DEP1 ^ CC_DEP2) & (CC_DEP1 ^ (CC_DEP1 - CC_DEP2)), DATA_BITS - 1) ;                            )\
   }                                                                                                                                \
}

/*-------------------------------------------------------------*/

#define ACTIONS_ADC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                                                 \
{                                                                                                                                   \
   PREAMBLE(DATA_BITS);                                                                                                             \
   {                                                                                                                                \
     auto oldC = CC_NDEP & AMD64G_CC_MASK_C;                                                                                        \
     /*ok*/MASKcf(return ite(oldC!=0ull,DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)) <= DATA_UTYPE(CC_DEP1),DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)) < DATA_UTYPE(CC_DEP1))  ;)\
     /*ok*/MASKpf(return parity_table(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC));                                                       )\
     /*ok*/MASKaf(return bit2ret((((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC) ^ CC_DEP1 ^ (CC_DEP2 ^ oldC)), AMD64G_CC_SHIFT_A);          )\
     /*ok*/MASKzf(return (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)) == 0ull) ;                                              )\
     /*ok*/MASKsf(return bit2ret(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC),  DATA_BITS - 1);                                            )\
     /*ok*/MASKof(return bit2ret((CC_DEP1 ^ (CC_DEP2 ^ oldC) ^ -1ull) & (CC_DEP1 ^ ((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)), DATA_BITS - 1) ;                                                                             )\
   }                                                                                                                                \
}

/*-------------------------------------------------------------*/

#define ACTIONS_SBB(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                                                                 \
{                                                                                                                                                   \
   PREAMBLE(DATA_BITS);                                                                                                                             \
   {                                                                                                                                                \
     auto oldC = CC_NDEP & AMD64G_CC_MASK_C;                                                                                                        \
     /*ok*/MASKcf(return  ite(oldC!=0ull, DATA_UTYPE(CC_DEP1) <= DATA_UTYPE((CC_DEP2 ^ oldC)),DATA_UTYPE(CC_DEP1) < DATA_UTYPE((CC_DEP2 ^ oldC)));  )\
     /*ok*/MASKpf(return parity_table(((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC));                                                                       )\
     /*ok*/MASKaf(return bit2ret((((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC) ^ CC_DEP1 ^ (CC_DEP2 ^ oldC)), AMD64G_CC_SHIFT_A);                          )\
     /*ok*/MASKzf(return (DATA_UTYPE(((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC)) == 0ull) ;                                                              )\
     /*ok*/MASKsf(return bit2ret(((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC),  DATA_BITS - 1);                                                            )\
     /*ok*/MASKof(return bit2ret((CC_DEP1 ^ (CC_DEP2 ^ oldC)) & (CC_DEP1 ^ ((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC)), DATA_BITS - 1) ;                 )\
   }                                                                                                                                                \
}

/*-------------------------------------------------------------*/

#define ACTIONS_LOGIC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                       \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKpf(return parity_table(CC_DEP1);                                                             )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0ull) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1,  DATA_BITS - 1);                                                  )\
     /*ok*/MASKof(return Vns((CC_DEP1), 0, 1);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_INC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                         \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return bit2ret(CC_NDEP,AMD64G_CC_SHIFT_C);                                                )\
     /*ok*/MASKpf(return parity_table(CC_DEP1);                                                             )\
     /*ok*/MASKaf(return bit2ret((CC_DEP1 ^ (CC_DEP1 - 1ull) ^ 1ull), AMD64G_CC_SHIFT_A);                   )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0ull) ;                                                    )\
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
     /*ok*/MASKcf(return bit2ret(CC_NDEP,AMD64G_CC_SHIFT_C);                                                )\
     /*ok*/MASKpf(return parity_table(CC_DEP1);                                                             )\
     /*ok*/MASKaf(return bit2ret((CC_DEP1 ^ (CC_DEP1 + 1ull) ^ 1ull), AMD64G_CC_SHIFT_A);                   )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0ull) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return ((CC_DEP1 & DATA_MASK) == ((ULong)SIGN_MASK - 1)) ;                                )\
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
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1); /* undefined */                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0ull) ;                                                    )\
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
     /*ok*/MASKcf(return bit2ret(CC_DEP2, AMD64G_CC_SHIFT_C);                                               )\
     /*ok*/MASKpf(return parity_table(CC_DEP1);                                                             )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1); /* undefined */                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0ull) ;                                                    )\
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
    /*ok*/MASKcf(  return bit2ret(CC_DEP1, AMD64G_CC_SHIFT_C);                                              )\
    /*ok*/MASKpf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_P);                                              )\
    /*ok*/MASKaf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_A);                                              )\
    /*ok*/MASKzf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_Z);                                              )\
    /*ok*/MASKsf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_S);                                              )\
    /*ok*/MASKof(  return bit2ret(CC_DEP1, DATA_BITS - 1).boolXor(bit2ret(CC_DEP1, 0));                     )\
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
    /*ok*/MASKpf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_P);                                              )\
    /*ok*/MASKaf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_A);                                              )\
    /*ok*/MASKzf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_Z);                                              )\
    /*ok*/MASKsf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_S);                                              )\
    /*ok*/MASKof(  return bit2ret(CC_DEP1, DATA_BITS - 1).boolXor(bit2ret(CC_DEP1, DATA_BITS - 2));         )\
   }                                                                                                        \
}


/*-------------------------------------------------------------*/

#define ACTIONS_ANDN(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                        \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKpf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0ull) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return Vns((CC_DEP1), 0, 1);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_BLSI(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                        \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return (DATA_UTYPE(CC_DEP2) != 0ull);                                                     )\
     /*ok*/MASKpf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0ull) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return Vns((CC_DEP1), 0, 1);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_BLSMSK(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                      \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return (DATA_UTYPE(CC_DEP2) == 0ull);                                                     )\
     /*ok*/MASKpf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKzf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return Vns((CC_DEP1), 0, 1);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_BLSR(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                        \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
     /*ok*/MASKcf(return (DATA_UTYPE(CC_DEP2) == 0ull);                                                     )\
     /*ok*/MASKpf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1);                                                              )\
     /*ok*/MASKzf(return (DATA_UTYPE(CC_DEP1) == 0ull) ;                                                    )\
     /*ok*/MASKsf(return bit2ret(CC_DEP1, DATA_BITS - 1);                                                   )\
     /*ok*/MASKof(return Vns((CC_DEP1), 0, 1);                                                              )\
   }                                                                                                        \
}

/*-------------------------------------------------------------*/

#define ACTIONS_ADCX(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)                        \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
    /*ok*/MASKcf({ auto oldOC = (CC_NDEP >> AMD64G_CC_SHIFT_C) & 1ull;                                      \
                   return ite(oldOC==1ull,                                                                  \
        (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) <= DATA_UTYPE(CC_DEP1)),                       \
        (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) < DATA_UTYPE(CC_DEP1)));    }                  )\
    /*ok*/MASKpf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_P);                                              )\
    /*ok*/MASKaf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_A);                                              )\
    /*ok*/MASKzf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_Z);                                              )\
    /*ok*/MASKsf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_S);                                              )\
    /*ok*/MASKof(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_O);                                              )\
   }                                                                                                        \
}

#define ACTIONS_ADOX(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE,FLAGNAME)               \
{                                                                                                           \
   PREAMBLE(DATA_BITS);                                                                                     \
   {                                                                                                        \
    /*ok*/MASKpf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_P);                                              )\
    /*ok*/MASKaf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_A);                                              )\
    /*ok*/MASKzf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_Z);                                              )\
    /*ok*/MASKsf(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_S);                                              )\
    /*ok*/MASKof(  return bit2ret(CC_NDEP, AMD64G_CC_SHIFT_O);                                              )\
        auto oldOC = (CC_NDEP >> AMD64G_CC_SHIFT_O) & 1ull;                                                 \
    /*ok*/MASKof(  return ite(oldOC==1ull,                                                                  \
        (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) <= DATA_UTYPE(CC_DEP1)),                       \
        (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) < DATA_UTYPE(CC_DEP1)));                       )\
   }                                                                                                        \
}


/*-------------------------------------------------------------*/

#define ACTIONS_UMUL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE, NARROWtoU,DATA_U2TYPE,NARROWto2U)           \
{                                                                                                                               \
   PREAMBLE(DATA_BITS);                                                                                                         \
   {                                                                                                                            \
     auto u2m = CC_DEP1.extract((sizeof(DATA_UTYPE) << 3) - 1, 0).zext(((sizeof(DATA_U2TYPE) - sizeof(DATA_UTYPE)) << 3))*      \
                CC_DEP2.extract((sizeof(DATA_UTYPE) << 3) - 1, 0).zext(((sizeof(DATA_U2TYPE) - sizeof(DATA_UTYPE)) << 3));      \
     /*ok*/MASKcf(return u2m.extract((sizeof(DATA_U2TYPE) << 3) - 1, DATA_BITS) != (DATA_UTYPE)0;                               )\
     /*ok*/MASKpf(return parity_table(u2m);                                                                                     )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1); /* undefined */                                                                  )\
     /*ok*/MASKzf(return (u2m.extract(DATA_BITS - 1, 0) == (DATA_UTYPE)0);                                                      )\
     /*ok*/MASKsf(return bit2ret(u2m, DATA_BITS - 1);                                                                           )\
     /*ok*/MASKof(return u2m.extract((sizeof(DATA_U2TYPE) << 3) - 1, DATA_BITS) != (DATA_UTYPE)0;                               )\
   }								                                                                                            \
}

/*-------------------------------------------------------------*/

#define ACTIONS_SMUL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_STYPE,NARROWtoS,DATA_S2TYPE,NARROWto2S)           \
{                                                                                                                               \
   PREAMBLE(DATA_BITS);                                                                                                         \
   {                                                                                                                            \
     auto u2m = CC_DEP1.extract((sizeof(DATA_STYPE) << 3) - 1, 0).sext(((sizeof(DATA_S2TYPE) - sizeof(DATA_STYPE)) << 3))*      \
                CC_DEP2.extract((sizeof(DATA_STYPE) << 3) - 1, 0).sext(((sizeof(DATA_S2TYPE) - sizeof(DATA_STYPE)) << 3));      \
     /*ok*/MASKcf(return u2m.extract((sizeof(DATA_S2TYPE) << 3) - 1, DATA_BITS) != ashr(u2m.extract(DATA_BITS - 1, 0),(DATA_BITS-1));)\
     /*ok*/MASKpf(return parity_table(u2m);                                                                                     )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1); /* undefined */                                                                  )\
     /*ok*/MASKzf(return (u2m.extract(DATA_BITS - 1, 0) == (DATA_STYPE)0);                                                      )\
     /*ok*/MASKsf(return bit2ret(u2m, DATA_BITS - 1);                                                                           )\
     /*ok*/MASKof(return u2m.extract((sizeof(DATA_S2TYPE) << 3) - 1, DATA_BITS) != ashr(u2m.extract(DATA_BITS - 1, 0),(DATA_BITS-1));)\
   }								                                                                                            \
}

/*-------------------------------------------------------------*/

#define ACTIONS_UMULQ(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof)                                                                \
{                                                                                                                               \
     auto u2m = CC_DEP1.extract(63, 0).zext(64)* CC_DEP2.extract(63, 0).zext(64);                                               \
     /*ok*/MASKcf(return u2m.extract(127, 64) != (ULong)0;                                                                      )\
     /*ok*/MASKpf(return parity_table(u2m);                                                                                     )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1); /* undefined */                                                                  )\
     /*ok*/MASKzf(return (u2m.extract(63, 0) == (ULong)0);                                                                      )\
     /*ok*/MASKsf(return bit2ret(u2m, 63);                                                                                      )\
     /*ok*/MASKof(return u2m.extract(127, 64) != (ULong)0;                                                                      )\
}

/*-------------------------------------------------------------*/

#define ACTIONS_SMULQ(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof)                                                                \
{                                                                                                                               \
     auto u2m = CC_DEP1.extract(63, 0).sext(64)*CC_DEP2.extract(63, 0).sext(64);                                                \
     /*ok*/MASKcf(return u2m.extract(127, 64) != ashr(u2m.extract(63, 0),63);                                                   )\
     /*ok*/MASKpf(return parity_table(u2m);                                                                                     )\
     /*ok*/MASKaf(return Vns((CC_DEP1), 0, 1); /* undefined */                                                                  )\
     /*ok*/MASKzf(return (u2m.extract(63, 0) == (ULong)0);                                                                      )\
     /*ok*/MASKsf(return bit2ret(u2m, 63);                                                                                      )\
     /*ok*/MASKof(return u2m.extract(127, 64) != ashr(u2m.extract(63, 0),63);                                                   )\
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


#define ACTIONS_UMULQ_cf()   ACTIONS_UMULQ     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_UMULQ_pf()   ACTIONS_UMULQ     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_UMULQ_af()   ACTIONS_UMULQ     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_UMULQ_zf()   ACTIONS_UMULQ     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_UMULQ_sf()   ACTIONS_UMULQ     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO)
#define ACTIONS_UMULQ_of()   ACTIONS_UMULQ     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO)

#define ACTIONS_SMULQ_cf()   ACTIONS_SMULQ     (MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_SMULQ_pf()   ACTIONS_SMULQ     (NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_SMULQ_af()   ACTIONS_SMULQ     (NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_SMULQ_zf()   ACTIONS_SMULQ     (NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO)
#define ACTIONS_SMULQ_sf()   ACTIONS_SMULQ     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO)
#define ACTIONS_SMULQ_of()   ACTIONS_SMULQ     (NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO)





#define z3_amd64g_calculate_rflags_(FLAG)                                                \
inline static Vns z3_amd64g_calculate_rflags_##FLAG(                                     \
    ULong cc_op,                                                                         \
    Vns &cc_dep1_formal,                                                                 \
    Vns &cc_dep2_formal,                                                                 \
    Vns &cc_ndep_formal)                                                                 \
{                                                                                        \
    switch (cc_op) {                                                                     \
    case AMD64G_CC_OP_COPY:   ACTIONS_COPY_##FLAG()                                      \
                                                                                         \
    case AMD64G_CC_OP_ADDB:   ACTIONS_ADD_##FLAG(8, UChar_extract);                      \
    case AMD64G_CC_OP_ADDW:   ACTIONS_ADD_##FLAG(16, UShort_extract);                    \
    case AMD64G_CC_OP_ADDL:   ACTIONS_ADD_##FLAG(32, UInt_extract);                      \
    case AMD64G_CC_OP_ADDQ:   ACTIONS_ADD_##FLAG(64, ULong_extract);                     \
                                                                                         \
    case AMD64G_CC_OP_ADCB:   ACTIONS_ADC_##FLAG(8, UChar_extract );                     \
    case AMD64G_CC_OP_ADCW:   ACTIONS_ADC_##FLAG(16, UShort_extract );                   \
    case AMD64G_CC_OP_ADCL:   ACTIONS_ADC_##FLAG(32, UInt_extract );                     \
    case AMD64G_CC_OP_ADCQ:   ACTIONS_ADC_##FLAG(64, ULong_extract );                    \
                                                                                         \
    case AMD64G_CC_OP_SUBB:   ACTIONS_SUB_##FLAG(8, UChar_extract );                     \
    case AMD64G_CC_OP_SUBW:   ACTIONS_SUB_##FLAG(16, UShort_extract );                   \
    case AMD64G_CC_OP_SUBL:   ACTIONS_SUB_##FLAG(32, UInt_extract );                     \
    case AMD64G_CC_OP_SUBQ:   ACTIONS_SUB_##FLAG(64, ULong_extract );                    \
                                                                                         \
    case AMD64G_CC_OP_SBBB:   ACTIONS_SBB_##FLAG(8, UChar_extract );                     \
    case AMD64G_CC_OP_SBBW:   ACTIONS_SBB_##FLAG(16, UShort_extract );                   \
    case AMD64G_CC_OP_SBBL:   ACTIONS_SBB_##FLAG(32, UInt_extract );                     \
    case AMD64G_CC_OP_SBBQ:   ACTIONS_SBB_##FLAG(64, ULong_extract );                    \
                                                                                         \
    case AMD64G_CC_OP_LOGICB: ACTIONS_LOGIC_##FLAG(8, UChar_extract );                   \
    case AMD64G_CC_OP_LOGICW: ACTIONS_LOGIC_##FLAG(16, UShort_extract );                 \
    case AMD64G_CC_OP_LOGICL: ACTIONS_LOGIC_##FLAG(32, UInt_extract );                   \
    case AMD64G_CC_OP_LOGICQ: ACTIONS_LOGIC_##FLAG(64, ULong_extract );                  \
                                                                                         \
    case AMD64G_CC_OP_INCB:   ACTIONS_INC_##FLAG(8, UChar_extract );                     \
    case AMD64G_CC_OP_INCW:   ACTIONS_INC_##FLAG(16, UShort_extract );                   \
    case AMD64G_CC_OP_INCL:   ACTIONS_INC_##FLAG(32, UInt_extract );                     \
    case AMD64G_CC_OP_INCQ:   ACTIONS_INC_##FLAG(64, ULong_extract );                    \
                                                                                         \
    case AMD64G_CC_OP_DECB:   ACTIONS_DEC_##FLAG(8, UChar_extract );                     \
    case AMD64G_CC_OP_DECW:   ACTIONS_DEC_##FLAG(16, UShort_extract );                   \
    case AMD64G_CC_OP_DECL:   ACTIONS_DEC_##FLAG(32, UInt_extract );                     \
    case AMD64G_CC_OP_DECQ:   ACTIONS_DEC_##FLAG(64, ULong_extract );                    \
                                                                                         \
    case AMD64G_CC_OP_SHLB:   ACTIONS_SHL_##FLAG(8, UChar_extract );                     \
    case AMD64G_CC_OP_SHLW:   ACTIONS_SHL_##FLAG(16, UShort_extract );                   \
    case AMD64G_CC_OP_SHLL:   ACTIONS_SHL_##FLAG(32, UInt_extract );                     \
    case AMD64G_CC_OP_SHLQ:   ACTIONS_SHL_##FLAG(64, ULong_extract );                    \
                                                                                         \
    case AMD64G_CC_OP_SHRB:   ACTIONS_SHR_##FLAG(8, UChar_extract );                     \
    case AMD64G_CC_OP_SHRW:   ACTIONS_SHR_##FLAG(16, UShort_extract );                   \
    case AMD64G_CC_OP_SHRL:   ACTIONS_SHR_##FLAG(32, UInt_extract );                     \
    case AMD64G_CC_OP_SHRQ:   ACTIONS_SHR_##FLAG(64, ULong_extract );                    \
                                                                                         \
    case AMD64G_CC_OP_ROLB:   ACTIONS_ROL_##FLAG(8, UChar_extract );                     \
    case AMD64G_CC_OP_ROLW:   ACTIONS_ROL_##FLAG(16, UShort_extract );                   \
    case AMD64G_CC_OP_ROLL:   ACTIONS_ROL_##FLAG(32, UInt_extract );                     \
    case AMD64G_CC_OP_ROLQ:   ACTIONS_ROL_##FLAG(64, ULong_extract );                    \
                                                                                         \
    case AMD64G_CC_OP_RORB:   ACTIONS_ROR_##FLAG(8, UChar_extract );                     \
    case AMD64G_CC_OP_RORW:   ACTIONS_ROR_##FLAG(16, UShort_extract );                   \
    case AMD64G_CC_OP_RORL:   ACTIONS_ROR_##FLAG(32, UInt_extract );                     \
    case AMD64G_CC_OP_RORQ:   ACTIONS_ROR_##FLAG(64, ULong_extract );                    \
                                                                                         \
                                                                                         \
    case AMD64G_CC_OP_ANDN32: ACTIONS_ANDN_##FLAG(32, UInt_extract);                     \
    case AMD64G_CC_OP_ANDN64: ACTIONS_ANDN_##FLAG(64, ULong_extract );                   \
                                                                                         \
    case AMD64G_CC_OP_BLSI32: ACTIONS_BLSI_##FLAG(32, UInt_extract );                    \
    case AMD64G_CC_OP_BLSI64: ACTIONS_BLSI_##FLAG(64, ULong_extract );                   \
                                                                                         \
    case AMD64G_CC_OP_BLSMSK32: ACTIONS_BLSMSK_##FLAG(32, UInt_extract );                \
    case AMD64G_CC_OP_BLSMSK64: ACTIONS_BLSMSK_##FLAG(64, ULong_extract );               \
                                                                                         \
    case AMD64G_CC_OP_BLSR32: ACTIONS_BLSR_##FLAG(32, UInt_extract );                    \
    case AMD64G_CC_OP_BLSR64: ACTIONS_BLSR_##FLAG(64, ULong_extract );                   \
                                                                                         \
    case AMD64G_CC_OP_ADCX32: ACTIONS_ADCX_##FLAG(32, UInt_extract);                     \
    case AMD64G_CC_OP_ADCX64: ACTIONS_ADCX_##FLAG(64, ULong_extract);                    \
                                                                                         \
    case AMD64G_CC_OP_ADOX32: ACTIONS_ADOX_##FLAG(32, UInt_extract);                     \
    case AMD64G_CC_OP_ADOX64: ACTIONS_ADOX_##FLAG(64, ULong_extract);                    \
                                                                                         \
                                                                                         \
    case AMD64G_CC_OP_UMULB:  ACTIONS_UMUL_##FLAG(8, UChar, toUChar,                     \
        UShort, toUShort);                                                               \
    case AMD64G_CC_OP_UMULW:  ACTIONS_UMUL_##FLAG(16, UShort, toUShort,                  \
        UInt, toUInt);                                                                   \
    case AMD64G_CC_OP_UMULL:  ACTIONS_UMUL_##FLAG(32, UInt, toUInt,                      \
        ULong, idULong);                                                                 \
                                                                                         \
    case AMD64G_CC_OP_UMULQ:  ACTIONS_UMULQ_##FLAG();                                    \
                                                                                         \
    case AMD64G_CC_OP_SMULB:  ACTIONS_SMUL_##FLAG(8, Char, toUChar,                      \
        Short, toUShort);                                                                \
    case AMD64G_CC_OP_SMULW:  ACTIONS_SMUL_##FLAG(16, Short, toUShort,                   \
        Int, toUInt);                                                                    \
    case AMD64G_CC_OP_SMULL:  ACTIONS_SMUL_##FLAG(32, Int, toUInt,                       \
        Long, idULong);                                                                  \
                                                                                         \
    case AMD64G_CC_OP_SMULQ:  ACTIONS_SMULQ_##FLAG();                                    \
                                                                                         \
    default:                                                                             \
        /* shouldn't really make these calls from generated code */                      \
        vex_printf("amd64g_calculate_rflags_all_WRK(AMD64)"                              \
            "( %llu, 0x%llx, 0x%llx, 0x%llx )\n",                                        \
            cc_op, cc_dep1_formal, cc_dep2_formal, cc_ndep_formal);                      \
        vpanic("amd64g_calculate_rflags_all_WRK(AMD64)");                                \
    }                                                                                    \
}






z3_amd64g_calculate_rflags_(cf);
z3_amd64g_calculate_rflags_(pf);
z3_amd64g_calculate_rflags_(af);
z3_amd64g_calculate_rflags_(zf);
z3_amd64g_calculate_rflags_(sf);
z3_amd64g_calculate_rflags_(of);



/* CALLED FROM GENERATED CODE: CLEAN HELPER */
/* returns 1 or 0 */

static inline Vns _z3_amd64g_calculate_condition(ULong/*AMD64Condcode*/ cond,
    ULong cc_op,
    Vns &cc_dep1,
    Vns &cc_dep2,
    Vns &cc_ndep)
{
    switch (cond) {
    case AMD64CondNO:
    case AMD64CondO: /* OF == 1 */
        return  z3_amd64g_calculate_rflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep);

    case AMD64CondNZ:
    case AMD64CondZ: /* ZF == 1 */
        return  z3_amd64g_calculate_rflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep);

    case AMD64CondNB:
    case AMD64CondB: /* CF == 1 */
        return  z3_amd64g_calculate_rflags_cf(cc_op, cc_dep1, cc_dep2, cc_ndep);

    case AMD64CondNBE:
    case AMD64CondBE: /* (CF or ZF) == 1 */
        return  z3_amd64g_calculate_rflags_cf(cc_op, cc_dep1, cc_dep2, cc_ndep) || z3_amd64g_calculate_rflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep);

    case AMD64CondNS:
    case AMD64CondS: /* SF == 1 */
        return  z3_amd64g_calculate_rflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep);

    case AMD64CondNP:
    case AMD64CondP: /* PF == 1 */
        return  z3_amd64g_calculate_rflags_pf(cc_op, cc_dep1, cc_dep2, cc_ndep);

    case AMD64CondNL:
    case AMD64CondL: /* (SF xor OF) == 1 */
        return z3_amd64g_calculate_rflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep).boolXor(z3_amd64g_calculate_rflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep));
          
    case AMD64CondNLE:
    case AMD64CondLE: /* ((SF xor OF) or ZF)  == 1 */ {
        auto sf = z3_amd64g_calculate_rflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep);
        auto of = z3_amd64g_calculate_rflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep);
        auto zf = z3_amd64g_calculate_rflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep);
        return   (sf.boolXor(of)) || zf;
    }
    default:
        /* shouldn't really make these calls from generated code */
        vex_printf("amd64g_calculate_condition"
            "( %llu, %llu, 0x%llx, 0x%llx, 0x%llx )\n",
            cond, cc_op, cc_dep1, cc_dep2, cc_ndep);
        vpanic("amd64g_calculate_condition");
    }
}


Vns z3_amd64g_calculate_condition(Vns/*AMD64Condcode*/ &cond,
    Vns &cc_op,
    Vns &cc_dep1,
    Vns &cc_dep2,
    Vns &cc_ndep)
{
    auto flag = _z3_amd64g_calculate_condition(cond, cc_op, cc_dep1, cc_dep2, cc_ndep);
    if (((ULong)cond & 1)) {
        flag = !  flag;
    }
    if (flag.real()) {
        return ((UChar)flag) ? Vns(cond, 1ull) : Vns(cond, 0ull);
    }
    else {
        return Vns(cond, Z3_mk_ite(cond, flag, Vns(cond, 1ull), Vns(cond, 0ull)), 64);
    }
}



inline Vns z3_amd64g_calculate_rflags_c(Vns &cc_op,
    Vns & cc_dep1,
    Vns & cc_dep2,
    Vns & cc_ndep)
{
    /* Fast-case some common ones. */
    switch ((int)cc_op) {
    case AMD64G_CC_OP_LOGICQ:
    case AMD64G_CC_OP_LOGICL:
    case AMD64G_CC_OP_LOGICW:
    case AMD64G_CC_OP_LOGICB:
        return Vns(cc_op, 0ull);
    default:
        break;
    }

    auto flag = z3_amd64g_calculate_rflags_cf(cc_op, cc_dep1, cc_dep2, cc_ndep);
    if (flag.real()) {
        return ((UChar)flag) ? Vns(cc_op, 1ull) : Vns(cc_op, 0ull);
    }
    else {
        return Vns(cc_op, Z3_mk_ite(cc_op, flag, Vns(cc_op, 1ull, 64), Vns(cc_op, 0ull, 64)), 64);
    }
}

Vns z3_amd64g_calculate_rflags_all(Vns& cc_op,
    Vns& cc_dep1,
    Vns& cc_dep2,
    Vns& cc_ndep)
{
    auto of = ite(z3_amd64g_calculate_rflags_of(cc_op, cc_dep1, cc_dep2, cc_ndep), Vns(cc_op, 0ull), Vns(cc_op, AMD64G_CC_MASK_O));
    auto sf = ite(z3_amd64g_calculate_rflags_sf(cc_op, cc_dep1, cc_dep2, cc_ndep), Vns(cc_op, 0ull), Vns(cc_op, AMD64G_CC_MASK_S));
    auto zf = ite(z3_amd64g_calculate_rflags_zf(cc_op, cc_dep1, cc_dep2, cc_ndep), Vns(cc_op, 0ull), Vns(cc_op, AMD64G_CC_MASK_Z));
    auto af = ite(z3_amd64g_calculate_rflags_af(cc_op, cc_dep1, cc_dep2, cc_ndep), Vns(cc_op, 0ull), Vns(cc_op, AMD64G_CC_MASK_A));
    auto cf = ite(z3_amd64g_calculate_rflags_cf(cc_op, cc_dep1, cc_dep2, cc_ndep), Vns(cc_op, 0ull), Vns(cc_op, AMD64G_CC_MASK_C));
    auto pf = ite(z3_amd64g_calculate_rflags_pf(cc_op, cc_dep1, cc_dep2, cc_ndep), Vns(cc_op, 0ull), Vns(cc_op, AMD64G_CC_MASK_P));
    return of | sf | zf | af | cf | pf;
}




#undef z3_amd64g_calculate_rflags_
#undef CC_DEP1
#undef CC_DEP2
#undef CC_NDEP
#undef PREAMBLE
#undef ACTIONS_COPY_cf
#undef ACTIONS_COPY_pf
#undef ACTIONS_COPY_af
#undef ACTIONS_COPY_zf
#undef ACTIONS_COPY_sf
#undef ACTIONS_COPY_of
#undef ACTIONS_ADD_cf
#undef ACTIONS_ADD_pf
#undef ACTIONS_ADD_af
#undef ACTIONS_ADD_zf
#undef ACTIONS_ADD_sf
#undef ACTIONS_ADD_of
#undef ACTIONS_ADC_cf
#undef ACTIONS_ADC_pf
#undef ACTIONS_ADC_af
#undef ACTIONS_ADC_zf
#undef ACTIONS_ADC_sf
#undef ACTIONS_ADC_of
#undef ACTIONS_SUB_cf
#undef ACTIONS_SUB_pf
#undef ACTIONS_SUB_af
#undef ACTIONS_SUB_zf
#undef ACTIONS_SUB_sf
#undef ACTIONS_SUB_of
#undef ACTIONS_SBB_cf
#undef ACTIONS_SBB_pf
#undef ACTIONS_SBB_af
#undef ACTIONS_SBB_zf
#undef ACTIONS_SBB_sf
#undef ACTIONS_SBB_of
#undef ACTIONS_LOGIC_cf
#undef ACTIONS_LOGIC_pf
#undef ACTIONS_LOGIC_af
#undef ACTIONS_LOGIC_zf
#undef ACTIONS_LOGIC_sf
#undef ACTIONS_LOGIC_of
#undef ACTIONS_INC_cf
#undef ACTIONS_INC_pf
#undef ACTIONS_INC_af
#undef ACTIONS_INC_zf
#undef ACTIONS_INC_sf
#undef ACTIONS_INC_of
#undef ACTIONS_DEC_cf
#undef ACTIONS_DEC_pf
#undef ACTIONS_DEC_af
#undef ACTIONS_DEC_zf
#undef ACTIONS_DEC_sf
#undef ACTIONS_DEC_of
#undef ACTIONS_SHL_cf
#undef ACTIONS_SHL_pf
#undef ACTIONS_SHL_af
#undef ACTIONS_SHL_zf
#undef ACTIONS_SHL_sf
#undef ACTIONS_SHL_of
#undef ACTIONS_SHR_cf
#undef ACTIONS_SHR_pf
#undef ACTIONS_SHR_af
#undef ACTIONS_SHR_zf
#undef ACTIONS_SHR_sf
#undef ACTIONS_SHR_of
#undef ACTIONS_ROL_cf
#undef ACTIONS_ROL_pf
#undef ACTIONS_ROL_af
#undef ACTIONS_ROL_zf
#undef ACTIONS_ROL_sf
#undef ACTIONS_ROL_of
#undef ACTIONS_ROR_cf
#undef ACTIONS_ROR_pf
#undef ACTIONS_ROR_af
#undef ACTIONS_ROR_zf
#undef ACTIONS_ROR_sf
#undef ACTIONS_ROR_of
#undef ACTIONS_ANDN_cf
#undef ACTIONS_ANDN_pf
#undef ACTIONS_ANDN_af
#undef ACTIONS_ANDN_zf
#undef ACTIONS_ANDN_sf
#undef ACTIONS_ANDN_of
#undef ACTIONS_BLSI_cf
#undef ACTIONS_BLSI_pf
#undef ACTIONS_BLSI_af
#undef ACTIONS_BLSI_zf
#undef ACTIONS_BLSI_sf
#undef ACTIONS_BLSI_of
#undef ACTIONS_BLSMSK_cf
#undef ACTIONS_BLSMSK_pf
#undef ACTIONS_BLSMSK_af
#undef ACTIONS_BLSMSK_zf
#undef ACTIONS_BLSMSK_sf
#undef ACTIONS_BLSMSK_of
#undef ACTIONS_BLSR_cf
#undef ACTIONS_BLSR_pf
#undef ACTIONS_BLSR_af
#undef ACTIONS_BLSR_zf
#undef ACTIONS_BLSR_sf
#undef ACTIONS_BLSR_of
#undef ACTIONS_ADCX_cf
#undef ACTIONS_ADCX_pf
#undef ACTIONS_ADCX_af
#undef ACTIONS_ADCX_zf
#undef ACTIONS_ADCX_sf
#undef ACTIONS_ADCX_of
#undef ACTIONS_ADOX_cf
#undef ACTIONS_ADOX_pf
#undef ACTIONS_ADOX_af
#undef ACTIONS_ADOX_zf
#undef ACTIONS_ADOX_sf
#undef ACTIONS_ADOX_of
#undef ACTIONS_UMUL_cf
#undef ACTIONS_UMUL_pf
#undef ACTIONS_UMUL_af
#undef ACTIONS_UMUL_zf
#undef ACTIONS_UMUL_sf
#undef ACTIONS_UMUL_of
#undef ACTIONS_SMUL_cf
#undef ACTIONS_SMUL_pf
#undef ACTIONS_SMUL_af
#undef ACTIONS_SMUL_zf
#undef ACTIONS_SMUL_sf
#undef ACTIONS_SMUL_of
#undef ACTIONS_UMULQ_cf
#undef ACTIONS_UMULQ_pf
#undef ACTIONS_UMULQ_af
#undef ACTIONS_UMULQ_zf
#undef ACTIONS_UMULQ_sf
#undef ACTIONS_UMULQ_of
#undef ACTIONS_SMULQ_cf
#undef ACTIONS_SMULQ_pf
#undef ACTIONS_SMULQ_af
#undef ACTIONS_SMULQ_zf
#undef ACTIONS_SMULQ_sf
#undef ACTIONS_SMULQ_of

#undef ACTIONS_COPY
#undef ACTIONS_ADD
#undef ACTIONS_ADC
#undef ACTIONS_SUB
#undef ACTIONS_SBB
#undef ACTIONS_LOGIC
#undef ACTIONS_INC
#undef ACTIONS_DEC
#undef ACTIONS_SHL
#undef ACTIONS_SHR
#undef ACTIONS_ROL
#undef ACTIONS_ROR
#undef ACTIONS_ANDN
#undef ACTIONS_BLSI
#undef ACTIONS_BLSMSK
#undef ACTIONS_BLSR
#undef ACTIONS_ADCX
#undef ACTIONS_ADOX
#undef ACTIONS_UMUL
#undef ACTIONS_SMUL
#undef ACTIONS_UMULQ
#undef ACTIONS_SMULQ