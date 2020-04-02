
#define bit2ret(v, idx) (rsbool(((v) >> (idx))))


#define NOTEMACRO(...)  
#define MACRO(...) __VA_ARGS__

#define UChar_extract(value) ((value).extract<7, 0>())
#define UShort_extract(value) ((value).extract<15, 0>())
#define UInt_extract(value) ((value).extract<31, 0>())
#define ULong_extract(value) (value)
//Z3_ast bv2bool(Z3_context ctx, Z3_ast ast);
rsbool parity_table(sv::rsval<true, 8, Z3_BV_SORT> const& d);
extern "C" unsigned int vex_printf(const HChar * format, ...);
extern "C" void vpanic(const HChar * str);
