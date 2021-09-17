#ifndef _Z3_TARGET_DEF_HEADER_
#define _Z3_TARGET_DEF_HEADER_
#define bit2ret(v, idx) (rsbool(  (v).extract<(idx), (idx)>()  ))


#define NOTEMACRO(...)  
#define MACRO(...) __VA_ARGS__

#define UChar_extract(value) ((value).extract<7, 0>())
#define UShort_extract(value) ((value).extract<15, 0>())
#define UInt_extract(value) ((value).extract<31, 0>())
#define ULong_extract(value) (value)
//Z3_ast bv2bool(Z3_context ctx, Z3_ast ast);
rsbool parity_table_8(sv::rsval<false, 8, Z3_BV_SORT> const& d);

template<bool sign, int nbits>
static rsbool parity_table(sv::rsval<sign, nbits, Z3_BV_SORT> const& d) { 
	return parity_table_8(d.template extract<7, 0>());
}
template<bool sign, int nbits>
static rsbool parity_table(sv::symbolic<sign, nbits, Z3_BV_SORT> const& d) {
	return parity_table_8(d.template extract<7, 0>());
}
#endif