
#define bit2ret(v, idx)  ((v).real()) ? Vns((Z3_context)(v), ((v)>>(idx)), 1) : Vns((Z3_context)(v), bv2bool((Z3_context)(v), Vns((Z3_context)(v),Z3_mk_extract(v,idx,idx,v),1)),1)


#define NOTEMACRO(...)  
#define MACRO(a) a

#define UChar_extract(value) ((value).extract(7,0))
#define UShort_extract(value) ((value).extract(15,0))
#define UInt_extract(value) ((value).extract(31,0))
#define ULong_extract(value) (value)
//Z3_ast bv2bool(Z3_context ctx, Z3_ast ast);
//Vns parity_table(Vns const& d);
extern "C" unsigned int vex_printf(const HChar * format, ...);
extern "C" void vpanic(const HChar * str);
