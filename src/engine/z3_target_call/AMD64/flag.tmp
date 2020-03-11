
#define NOTEMACRO(...)  
#define MACRO(a) a

#define CC_DEP1 cc_dep1_formal
#define CC_DEP2 cc_dep2_formal
#define CC_NDEP cc_ndep_formal


auto parity_table = [](expr &d) {
	expr all = d.extract(0, 0);
	for (UChar i = 1; i <= 7; i++) {
		all = all + d.extract(i, i);
	}
	return all.extract(0, 0) == d.ctx().bv_val(0,1);
};


inline expr operator&(expr const & a, unsigned long long b) { return a & expr(a.ctx(), Z3_mk_int64(a.ctx(), b, a.get_sort())); };
inline expr operator&(unsigned long long b,expr const & a ) { return a & expr(a.ctx(), Z3_mk_int64(a.ctx(), b, a.get_sort())); };


inline expr operator<<(expr const & a, int b) { return expr(a.ctx(), Z3_mk_bvshl(a.ctx(),a, expr(a.ctx(), Z3_mk_int64(a.ctx(), b, a.get_sort())))); };
inline expr operator<<(expr const & a, expr const b) { return expr(a.ctx(), Z3_mk_bvshl(a.ctx(), a, b)); };

inline expr operator>>(expr const & a, int b) { return expr(a.ctx(), Z3_mk_bvlshr(a.ctx(), a, expr(a.ctx(), Z3_mk_int64(a.ctx(), b, a.get_sort())))); };
inline expr operator>>(expr const & a, expr const b) { return expr(a.ctx(), Z3_mk_bvlshr(a.ctx(), a, b)); };

inline expr operator==(expr const & a, ULong b) { return a == expr(a.ctx(), Z3_mk_unsigned_int64(a.ctx(), b, a.get_sort())); };



#define UChar_extract(value) (value.extract(7,0))
#define UShort_extract(value) (value.extract(15,0))
#define UInt_extract(value) (value.extract(31,0))
#define ULong_extract(value) (value)
#define lshift(exp,bitn)   (((exp).extract(-(bitn), -(bitn)) )==1)

static inline expr lshift_o ( expr &x, Int n )
{
   if (n >= 0)
      return x << n;
   else
      return ashr(x , -n);
}


#define PREAMBLE(__data_bits)									\
   /* const */ ULong DATA_MASK 									\
      = __data_bits==8                                          \
           ? 0xFFULL 											\
           : (__data_bits==16                                   \
                ? 0xFFFFULL 									\
                : (__data_bits==32                              \
                     ? 0xFFFFFFFFULL                            \
                     : 0xFFFFFFFFFFFFFFFFULL));                 \
   /* const */ ULong SIGN_MASK = 1ULL << (__data_bits - 1);     \


/*-------------------------------------------------------------*/

#define ACTIONS_ADD(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{											\
   PREAMBLE(DATA_BITS);						\
   {										\
     MASKcf(return DATA_UTYPE((CC_DEP1 + CC_DEP2)) < DATA_UTYPE(CC_DEP1);			)\
     MASKpf(return parity_table((CC_DEP1 + CC_DEP2));					)\
     MASKaf(return ((CC_DEP1 + CC_DEP2) ^ CC_DEP1 ^ CC_DEP2).extract(AMD64G_CC_SHIFT_A,AMD64G_CC_SHIFT_A) == 1;					)\
     MASKzf(return (DATA_UTYPE((CC_DEP1 + CC_DEP2)) == 0) ;					)\
     MASKsf(return lshift((CC_DEP1 + CC_DEP2), 8 - DATA_BITS- AMD64G_CC_SHIFT_O) ;			)\
     MASKof(return lshift((CC_DEP1 ^ CC_DEP2 ^ -1) & (CC_DEP1 ^ (CC_DEP1 + CC_DEP2)), 	\
                 12 - DATA_BITS - AMD64G_CC_SHIFT_O) ;			)\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_SUB(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{								\
   PREAMBLE(DATA_BITS);						\
   { 				\
     MASKcf(return DATA_UTYPE(CC_DEP1) < DATA_UTYPE(CC_DEP2);			)\
     MASKpf(return parity_table((CC_DEP1 - CC_DEP2));					)\
     MASKaf(return ((CC_DEP1 - CC_DEP2) ^ CC_DEP1 ^ CC_DEP2) .extract(AMD64G_CC_SHIFT_A,AMD64G_CC_SHIFT_A) == 1;		)\
     MASKzf(return (DATA_UTYPE((CC_DEP1 - CC_DEP2)) == 0) ;					)\
     MASKsf(return lshift((CC_DEP1 - CC_DEP2), 8 - DATA_BITS - AMD64G_CC_SHIFT_S);			)\
     MASKof(return lshift((CC_DEP1 ^ CC_DEP2) & (CC_DEP1 ^ (CC_DEP1 - CC_DEP2)),	 		\
                 12 - DATA_BITS - AMD64G_CC_SHIFT_O) ; 			)\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_ADC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																\
   PREAMBLE(DATA_BITS);											\
   { 															\
     auto oldC = CC_NDEP & AMD64G_CC_MASK_C;					\
     MASKcf(return ite(oldC!=(CC_DEP1).ctx().bv_val(0,64),DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)) <= DATA_UTYPE(CC_DEP1),DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)) < DATA_UTYPE(CC_DEP1))  ;		)\
     MASKpf(return parity_table(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC));					)\
     MASKaf(return (((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC) ^ CC_DEP1 ^ (CC_DEP2 ^ oldC)) .extract(AMD64G_CC_SHIFT_A,AMD64G_CC_SHIFT_A) == 1;					)\
     MASKzf(return (DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)) == 0) ;					)\
     MASKsf(return lshift(((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC), 8 - DATA_BITS - AMD64G_CC_SHIFT_S);			)\
     MASKof(return lshift((CC_DEP1 ^ (CC_DEP2 ^ oldC) ^ -1) & (CC_DEP1 ^ ((CC_DEP1 + (CC_DEP2 ^ oldC)) + oldC)), 	\
                  12 - DATA_BITS - AMD64G_CC_SHIFT_O) ;			)\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_SBB(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																\
   PREAMBLE(DATA_BITS);											\
   { 															\
     auto oldC = CC_NDEP & AMD64G_CC_MASK_C;					\
     MASKcf(return  ite(oldC!=(CC_DEP1).ctx().bv_val(0,64), DATA_UTYPE(CC_DEP1) <= DATA_UTYPE((CC_DEP2 ^ oldC)),DATA_UTYPE(CC_DEP1) < DATA_UTYPE((CC_DEP2 ^ oldC)));		)\
     MASKpf(return parity_table(((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC));					)\
     MASKaf(return (((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC) ^ CC_DEP1 ^ (CC_DEP2 ^ oldC)) .extract(AMD64G_CC_SHIFT_A,AMD64G_CC_SHIFT_A) == 1;					)\
     MASKzf(return (DATA_UTYPE(((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC)) == 0) ;					)\
     MASKsf(return lshift(((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC), 8 - DATA_BITS - AMD64G_CC_SHIFT_S);			)\
     MASKof(return lshift((CC_DEP1 ^ (CC_DEP2 ^ oldC)) & (CC_DEP1 ^ ((CC_DEP1 - (CC_DEP2 ^ oldC)) - oldC)), 		\
                 12 - DATA_BITS - AMD64G_CC_SHIFT_O) ;			)\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_LOGIC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																\
   PREAMBLE(DATA_BITS);											\
   { 															\
     MASKcf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKpf(return parity_table(CC_DEP1);				)\
     MASKaf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;				)\
     MASKsf(return lshift(CC_DEP1, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);		)\
     MASKof(return (CC_DEP1).ctx().bool_val(False);											)\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_INC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{															\
   PREAMBLE(DATA_BITS);										\
   { 														\
     MASKcf(return (CC_NDEP).extract(AMD64G_CC_SHIFT_C,AMD64G_CC_SHIFT_C) == 1;				)\
     MASKpf(return parity_table(CC_DEP1);				)\
     MASKaf(return (CC_DEP1 ^ (CC_DEP1 - 1) ^ 1) .extract(AMD64G_CC_SHIFT_A,AMD64G_CC_SHIFT_A) == 1;				)\
     MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;				)\
     MASKsf(return lshift(CC_DEP1, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);		)\
     MASKof(return ((CC_DEP1 & DATA_MASK) == SIGN_MASK) ;	)\
     														\
   }														\
}

/*-------------------------------------------------------------*/

#define ACTIONS_DEC(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{															\
   PREAMBLE(DATA_BITS);										\
   { 														\
     MASKcf(return (CC_NDEP).extract(AMD64G_CC_SHIFT_C,AMD64G_CC_SHIFT_C) == 1;				)\
     MASKpf(return parity_table(CC_DEP1);				)\
     MASKaf(return (CC_DEP1 ^ (CC_DEP1 + 1) ^ 1) .extract(AMD64G_CC_SHIFT_A,AMD64G_CC_SHIFT_A) == 1;				)\
     MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;				)\
     MASKsf(return lshift(CC_DEP1, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);		)\
     MASKof(return ((CC_DEP1 & DATA_MASK) 						\
          == ((ULong)SIGN_MASK - 1)) ;					)\
     														\
   }														\
}

/*-------------------------------------------------------------*/

#define ACTIONS_SHL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																		\
   PREAMBLE(DATA_BITS);													\
   { 																	\
     MASKcf(return (CC_DEP2 >> (DATA_BITS - 1)).extract(AMD64G_CC_SHIFT_C,AMD64G_CC_SHIFT_C) == 1;		)\
     MASKpf(return parity_table(CC_DEP1);						)\
     MASKaf(return (CC_DEP1).ctx().bool_val(False); /* undefined */									)\
     MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;						)\
     MASKsf(return lshift(CC_DEP1, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);				)\
     /* of is defined if shift count == 1 */							\
     MASKof(return lshift(CC_DEP2 ^ CC_DEP1, 12 - DATA_BITS - AMD64G_CC_SHIFT_O);)\
   }																	\
}

/*-------------------------------------------------------------*/

#define ACTIONS_SHR(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																		\
   PREAMBLE(DATA_BITS);  												\
   { 																	\
     MASKcf(return (CC_DEP2).extract(0,0) == 1;											)\
     MASKpf(return parity_table(CC_DEP1);						)\
     MASKaf(return (CC_DEP1).ctx().bool_val(False); /* undefined */									)\
     MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;						)\
     MASKsf(return lshift(CC_DEP1, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);				)\
     /* of is defined if shift count == 1 */							\
     MASKof(return lshift(CC_DEP2 ^ CC_DEP1, 12 - DATA_BITS - AMD64G_CC_SHIFT_O);)\
   }																	\
}

/*-------------------------------------------------------------*/

/* ROL: cf' = lsb(result).  of' = msb(result) ^ lsb(result). */
/* DEP1 = result, NDEP = old flags */
#define ACTIONS_ROL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																			\
   PREAMBLE(DATA_BITS);														\
   { auto fl 																\
        = (CC_NDEP & ~(AMD64G_CC_MASK_O | AMD64G_CC_MASK_C))				\
          | (AMD64G_CC_MASK_C & CC_DEP1)									\
          | (AMD64G_CC_MASK_O & (lshift_o(CC_DEP1,					 		\
                                      11-(DATA_BITS-1))						\
                     ^ lshift_o(CC_DEP1, 11)));								\
    MASKcf(  return fl.extract(AMD64G_CC_SHIFT_C,AMD64G_CC_SHIFT_C) == 1 ;  )  \
    MASKpf(  return fl.extract(AMD64G_CC_SHIFT_P,AMD64G_CC_SHIFT_P) == 1 ;  )  \
    MASKaf(  return fl.extract(AMD64G_CC_SHIFT_A,AMD64G_CC_SHIFT_A) == 1 ;  )  \
    MASKzf(  return fl.extract(AMD64G_CC_SHIFT_Z,AMD64G_CC_SHIFT_Z) == 1 ;  )  \
    MASKsf(  return fl.extract(AMD64G_CC_SHIFT_S,AMD64G_CC_SHIFT_S) == 1 ;  )  \
    MASKof(  return fl.extract(AMD64G_CC_SHIFT_O,AMD64G_CC_SHIFT_O) == 1 ;  )  \
   }																		\
}

/*-------------------------------------------------------------*/

/* ROR: cf' = msb(result).  of' = msb(result) ^ msb-1(result). */
/* DEP1 = result, NDEP = old flags */
#define ACTIONS_ROR(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																			\
   PREAMBLE(DATA_BITS);														\
   { auto fl 																\
        = (CC_NDEP & ~(AMD64G_CC_MASK_O | AMD64G_CC_MASK_C))				\
          | (AMD64G_CC_MASK_C & (CC_DEP1 >> (DATA_BITS-1)))					\
          | (AMD64G_CC_MASK_O & (lshift_o(CC_DEP1, 							\
                                      11-(DATA_BITS-1)) 					\
                     ^ lshift_o(CC_DEP1, 11-(DATA_BITS-1)+1)));				\
    MASKcf(  return fl.extract(AMD64G_CC_SHIFT_C,AMD64G_CC_SHIFT_C) == 1 ;  )  \
    MASKpf(  return fl.extract(AMD64G_CC_SHIFT_P,AMD64G_CC_SHIFT_P) == 1 ;  )  \
    MASKaf(  return fl.extract(AMD64G_CC_SHIFT_A,AMD64G_CC_SHIFT_A) == 1 ;  )  \
    MASKzf(  return fl.extract(AMD64G_CC_SHIFT_Z,AMD64G_CC_SHIFT_Z) == 1 ;  )  \
    MASKsf(  return fl.extract(AMD64G_CC_SHIFT_S,AMD64G_CC_SHIFT_S) == 1 ;  )  \
    MASKof(  return fl.extract(AMD64G_CC_SHIFT_O,AMD64G_CC_SHIFT_O) == 1 ;  )  \
   }																		\
}


/*-------------------------------------------------------------*/

#define ACTIONS_ANDN(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																\
   PREAMBLE(DATA_BITS);											\
   { 															\
     MASKcf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKpf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKaf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;				)\
     MASKsf(return lshift(CC_DEP1, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);		)\
     MASKof(return (CC_DEP1).ctx().bool_val(False);											)\
     															\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_BLSI(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																\
   PREAMBLE(DATA_BITS);											\
   { 															\
     MASKcf(return (DATA_UTYPE(CC_DEP2) != 0);					)\
     MASKpf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKaf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;				)\
     MASKsf(return lshift(CC_DEP1, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);		)\
     MASKof(return (CC_DEP1).ctx().bool_val(False);											)\
     															\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_BLSMSK(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																\
   PREAMBLE(DATA_BITS);											\
   {                            								\
     MASKcf(return (DATA_UTYPE(CC_DEP2) == 0);					)\
     MASKpf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKaf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKzf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKsf(return lshift(CC_DEP1, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);		)\
     MASKof(return (CC_DEP1).ctx().bool_val(False);											)\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_BLSR(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE)			\
{																\
   PREAMBLE(DATA_BITS);											\
   { 															\
     MASKcf(return (DATA_UTYPE(CC_DEP2) == 0);					)\
     MASKpf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKaf(return (CC_DEP1).ctx().bool_val(False);											)\
     MASKzf(return (DATA_UTYPE(CC_DEP1) == 0) ;				)\
     MASKsf(return lshift(CC_DEP1, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);		)\
     MASKof(return (CC_DEP1).ctx().bool_val(False);											)\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_ADX(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,DATA_UTYPE,FLAGNAME)	\
{														                                        \
   PREAMBLE(DATA_BITS);									                                        \
   {                                        			                                        \
    auto oldOC = (CC_NDEP >> AMD64G_CC_SHIFT_##FLAGNAME) & 1;	                                \
    auto RES = ite(oldOC == 1,                              \
        (CC_NDEP & ~AMD64G_CC_MASK_##FLAGNAME) | ((DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) <= DATA_UTYPE(CC_DEP1)) << AMD64G_CC_SHIFT_##FLAGNAME),\
        (CC_NDEP & ~AMD64G_CC_MASK_##FLAGNAME) | ((DATA_UTYPE(((CC_DEP1 + (CC_DEP2 ^ oldOC)) + oldOC)) < DATA_UTYPE(CC_DEP1)) << AMD64G_CC_SHIFT_##FLAGNAME)  \
    );	                                                                                        \
    MASKcf(  return RES.extract(AMD64G_CC_SHIFT_C,AMD64G_CC_SHIFT_C) == 1 ;  )                   \
    MASKpf(  return RES.extract(AMD64G_CC_SHIFT_P,AMD64G_CC_SHIFT_P) == 1 ;  )                   \
    MASKaf(  return RES.extract(AMD64G_CC_SHIFT_A,AMD64G_CC_SHIFT_A) == 1 ;  )                   \
    MASKzf(  return RES.extract(AMD64G_CC_SHIFT_Z,AMD64G_CC_SHIFT_Z) == 1 ;  )                   \
    MASKsf(  return RES.extract(AMD64G_CC_SHIFT_S,AMD64G_CC_SHIFT_S) == 1 ;  )                   \
    MASKof(  return RES.extract(AMD64G_CC_SHIFT_O,AMD64G_CC_SHIFT_O) == 1 ;  )                   \
   }													                                        \
}







static inline Bool toBool ( Int x ) {
   Int r = (x == 0) ? False : True;
   return (Bool)r;
}
static inline UChar toUChar ( Int x ) {
   x &= 0xFF;
   return (UChar)x;
}
static inline HChar toHChar ( Int x ) {
   x &= 0xFF;
   return (HChar)x;
}
static inline UShort toUShort ( Int x ) {
   x &= 0xFFFF;
   return (UShort)x;
}
static inline Short toShort ( Int x ) {
   x &= 0xFFFF;
   return (Short)x;
}
static inline UInt toUInt ( Long x ) {
   x &= 0xFFFFFFFFLL;
   return (UInt)x;
}

																			
	/*case AMD64G_CC_OP_UMULB:  ACTIONS_UMUL_##FLAG(8, UChar, toUChar,		
		UShort, toUShort);													
	case AMD64G_CC_OP_UMULW:  ACTIONS_UMUL_##FLAG(16, UShort, toUShort,		
		UInt, toUInt);														
	case AMD64G_CC_OP_UMULL:  ACTIONS_UMUL_##FLAG(32, UInt, toUInt,			
		ULong, idULong);													
																			
	case AMD64G_CC_OP_UMULQ:  ACTIONS_UMULQ_;								
																			
	case AMD64G_CC_OP_SMULB:  ACTIONS_SMUL_##FLAG(8, Char, toUChar,			
		Short, toUShort);				  									
	case AMD64G_CC_OP_SMULW:  ACTIONS_SMUL_##FLAG(16, Short, toUShort,		
		Int, toUInt);					  									
	case AMD64G_CC_OP_SMULL:  ACTIONS_SMUL_##FLAG(32, Int, toUInt,			
		Long, idULong);														
																			
	case AMD64G_CC_OP_SMULQ:  ACTIONS_SMULQ_;								
	case AMD64G_CC_OP_ADCX32: ACTIONS_ADX_##FLAG(32, UInt, C );				
	case AMD64G_CC_OP_ADCX64: ACTIONS_ADX_##FLAG(64, ULong, C );			
																			
	case AMD64G_CC_OP_ADOX32: ACTIONS_ADX_##FLAG(32, UInt, O );				
	case AMD64G_CC_OP_ADOX64: ACTIONS_ADX_##FLAG(64, ULong, O );*/			
															




/*-------------------------------------------------------------*/

#define ACTIONS_UMUL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,   DATA_UTYPE,  NARROWtoU,         \
                                                                            DATA_U2TYPE, NARROWto2U)        \
{                                                               \
   PREAMBLE(DATA_BITS);                                         \
   {															\
     DATA_UTYPE  hi;                                            \
     DATA_UTYPE  lo                                             \
        = NARROWtoU( (  DATA_UTYPE(CC_DEP1)  )                      \
                     * (   DATA_UTYPE(CC_DEP2)   ) );                 \
     DATA_U2TYPE rr                                             \
        = NARROWto2U(                                           \
             (   (DATA_U2TYPE)(  DATA_UTYPE(CC_DEP1)   )))               \
             * ((DATA_U2TYPE)(DATA_UTYPE(CC_DEP2)))) );          \
     hi = NARROWtoU(rr >>/*u*/ DATA_BITS);                      \
     MASKcf(return (hi != 0);                                   )\
     MASKpf(return parity_table(lo);                     )\
     MASKaf(return (CC_DEP1).ctx().bool_val(False); /* undefined */                           )\
     MASKzf(return (lo == 0) ;                              )\
     MASKsf(return lshift(lo, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);            )\
     MASKof(return hi != 0 ;                                    )\
   }															\
}

/*-------------------------------------------------------------*/

#define ACTIONS_SMUL(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof,DATA_BITS,   DATA_STYPE,  NARROWtoS,         \
                                                                            DATA_S2TYPE, NARROWto2S)				\
{																		\
   PREAMBLE(DATA_BITS);													\
   {																	\
     DATA_STYPE  hi;													\
     DATA_STYPE  lo														\
        = NARROWtoS( ((DATA_S2TYPE)(DATA_STYPE)CC_DEP1)					\
                     * ((DATA_S2TYPE)(DATA_STYPE)CC_DEP2) );			\
     DATA_S2TYPE rr														\
        = NARROWto2S(													\
             ((DATA_S2TYPE)((DATA_STYPE)CC_DEP1))						\
             * ((DATA_S2TYPE)((DATA_STYPE)CC_DEP2)) );					\
     hi = NARROWtoS(rr >>/*s*/ DATA_BITS);								\
     MASKcf(return (hi != (lo >>/*s*/ (DATA_BITS-1)));                  )\
     MASKpf(return parity_table(lo);                             )\
     MASKaf(return (CC_DEP1).ctx().bool_val(False); /* undefined */                                   )\
     MASKzf(return (lo == 0) ;                                      )\
     MASKsf(return lshift(lo, 8 - DATA_BITS - AMD64G_CC_SHIFT_S);                    )\
     MASKof(return (hi != (lo >>/*s*/ (DATA_BITS-1)));                                            )\
   }																	\
}

/*-------------------------------------------------------------*/

#define ACTIONS_UMULQ(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof)                                          \
{																		\
   PREAMBLE(64);														\
   {																	\
     ULong lo, hi;														\
     mullU64( (ULong)CC_DEP1, (ULong)CC_DEP2, &hi, &lo );				\
     MASKcf(return (hi != 0);                                           )\
     MASKpf(return parity_table(lo);                             )\
     MASKaf(return (CC_DEP1).ctx().bool_val(False); /* undefined */                                   )\
     MASKzf(return (lo == 0) ;                                      )\
     MASKsf(return lshift(lo, 8 - 64) & 0x80;                           )\
     MASKof(return (hi != 0);                                            )\
   }																	\
}

/*-------------------------------------------------------------*/

#define ACTIONS_SMULQ(MASKcf,MASKpf,MASKaf,MASKzf,MASKsf,MASKof)                                           \
{																		\
   PREAMBLE(64);													    \
   {																	\
     Long lo, hi;														\
     mullS64( (Long)CC_DEP1, (Long)CC_DEP2, &hi, &lo );					\
     MASKcf(return (hi != (lo >>/*s*/ (64-1)));                         )\
     MASKpf(return parity_table(lo);                             )\
     MASKaf(return (CC_DEP1).ctx().bool_val(False); /* undefined */                                   )\
     MASKzf(return (lo == 0) ;                                      )\
     MASKsf(return lshift(lo, 8 - 64) & 0x80;                           )\
     MASKof(return (hi != (lo >>/*s*/ (64-1)));                                            )\
   }																	\
}


/*-------------------------------------------------------------*/



#define ACTIONS_ADD_cf(A, B) ACTIONS_ADD(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_pf(A, B) ACTIONS_ADD(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_af(A, B) ACTIONS_ADD(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_zf(A, B) ACTIONS_ADD(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_sf(A, B) ACTIONS_ADD(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ADD_of(A, B) ACTIONS_ADD(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ADC_cf(A, B) ACTIONS_ADC(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_pf(A, B) ACTIONS_ADC(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_af(A, B) ACTIONS_ADC(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_zf(A, B) ACTIONS_ADC(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_sf(A, B) ACTIONS_ADC(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ADC_of(A, B) ACTIONS_ADC(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_SUB_cf(A, B) ACTIONS_SUB(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_pf(A, B) ACTIONS_SUB(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_af(A, B) ACTIONS_SUB(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_zf(A, B) ACTIONS_SUB(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_sf(A, B) ACTIONS_SUB(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_SUB_of(A, B) ACTIONS_SUB(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_SBB_cf(A, B) ACTIONS_SBB(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_pf(A, B) ACTIONS_SBB(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_af(A, B) ACTIONS_SBB(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_zf(A, B) ACTIONS_SBB(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_sf(A, B) ACTIONS_SBB(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_SBB_of(A, B) ACTIONS_SBB(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_LOGIC_cf(A, B) ACTIONS_LOGIC(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_pf(A, B) ACTIONS_LOGIC(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_af(A, B) ACTIONS_LOGIC(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_zf(A, B) ACTIONS_LOGIC(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_sf(A, B) ACTIONS_LOGIC(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_LOGIC_of(A, B) ACTIONS_LOGIC(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_INC_cf(A, B) ACTIONS_INC(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_pf(A, B) ACTIONS_INC(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_af(A, B) ACTIONS_INC(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_zf(A, B) ACTIONS_INC(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_sf(A, B) ACTIONS_INC(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_INC_of(A, B) ACTIONS_INC(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_DEC_cf(A, B) ACTIONS_DEC(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_pf(A, B) ACTIONS_DEC(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_af(A, B) ACTIONS_DEC(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_zf(A, B) ACTIONS_DEC(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_sf(A, B) ACTIONS_DEC(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_DEC_of(A, B) ACTIONS_DEC(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_SHL_cf(A, B) ACTIONS_SHL(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_pf(A, B) ACTIONS_SHL(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_af(A, B) ACTIONS_SHL(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_zf(A, B) ACTIONS_SHL(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_sf(A, B) ACTIONS_SHL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_SHL_of(A, B) ACTIONS_SHL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_SHR_cf(A, B) ACTIONS_SHR(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_pf(A, B) ACTIONS_SHR(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_af(A, B) ACTIONS_SHR(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_zf(A, B) ACTIONS_SHR(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_sf(A, B) ACTIONS_SHR(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_SHR_of(A, B) ACTIONS_SHR(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ROL_cf(A, B) ACTIONS_ROL(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_pf(A, B) ACTIONS_ROL(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_af(A, B) ACTIONS_ROL(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_zf(A, B) ACTIONS_ROL(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_sf(A, B) ACTIONS_ROL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ROL_of(A, B) ACTIONS_ROL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ROR_cf(A, B) ACTIONS_ROR(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_pf(A, B) ACTIONS_ROR(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_af(A, B) ACTIONS_ROR(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_zf(A, B) ACTIONS_ROR(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_sf(A, B) ACTIONS_ROR(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ROR_of(A, B) ACTIONS_ROR(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ANDN_cf(A, B) ACTIONS_ANDN(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_pf(A, B) ACTIONS_ANDN(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_af(A, B) ACTIONS_ANDN(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_zf(A, B) ACTIONS_ANDN(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_sf(A, B) ACTIONS_ANDN(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_ANDN_of(A, B) ACTIONS_ANDN(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_BLSI_cf(A, B) ACTIONS_BLSI(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_pf(A, B) ACTIONS_BLSI(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_af(A, B) ACTIONS_BLSI(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_zf(A, B) ACTIONS_BLSI(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_sf(A, B) ACTIONS_BLSI(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSI_of(A, B) ACTIONS_BLSI(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_BLSMSK_cf(A, B) ACTIONS_BLSMSK(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_pf(A, B) ACTIONS_BLSMSK(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_af(A, B) ACTIONS_BLSMSK(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_zf(A, B) ACTIONS_BLSMSK(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_sf(A, B) ACTIONS_BLSMSK(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSMSK_of(A, B) ACTIONS_BLSMSK(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_BLSR_cf(A, B) ACTIONS_BLSR(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_pf(A, B) ACTIONS_BLSR(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_af(A, B) ACTIONS_BLSR(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_zf(A, B) ACTIONS_BLSR(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_sf(A, B) ACTIONS_BLSR(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_BLSR_of(A, B) ACTIONS_BLSR(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_UMUL_cf(A, B) ACTIONS_UMUL(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_UMUL_pf(A, B) ACTIONS_UMUL(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_UMUL_af(A, B) ACTIONS_UMUL(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_UMUL_zf(A, B) ACTIONS_UMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_UMUL_sf(A, B) ACTIONS_UMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_UMUL_of(A, B) ACTIONS_UMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_SMUL_cf(A, B) ACTIONS_SMUL(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SMUL_pf(A, B) ACTIONS_SMUL(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SMUL_af(A, B) ACTIONS_SMUL(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SMUL_zf(A, B) ACTIONS_SMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B)
#define ACTIONS_SMUL_sf(A, B) ACTIONS_SMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B)
#define ACTIONS_SMUL_of(A, B) ACTIONS_SMUL(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B)
#define ACTIONS_ADX_cf(A, B, C) ACTIONS_ADX(MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B, C)
#define ACTIONS_ADX_pf(A, B, C) ACTIONS_ADX(NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B, C)
#define ACTIONS_ADX_af(A, B, C) ACTIONS_ADX(NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, A, B, C)
#define ACTIONS_ADX_zf(A, B, C) ACTIONS_ADX(NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, NOTEMACRO, A, B, C)
#define ACTIONS_ADX_sf(A, B, C) ACTIONS_ADX(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, NOTEMACRO, A, B, C)
#define ACTIONS_ADX_of(A, B, C) ACTIONS_ADX(NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, NOTEMACRO, MACRO, A, B, C)
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

