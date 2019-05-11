#include "Variable_CD.hpp"
#pragma once
#ifndef VARIABLE_D
#define VARIABLE_D

static inline void intString2bytes(unsigned char *bytesbuff, size_t n, const char * int_str) {
	PyObject *value = PyLong_FromString(int_str, 0, 10);
	_PyLong_AsByteArray((PyLongObject*)value, bytesbuff, n, 1, 0);
}

using namespace z3;


    inline void Variable::operator = (expr &a){ (*this) = Variable(a.ctx(),a); }

	inline Variable::Variable() :m_ast(NULL),bitn(8),m_ctx(0) {};//G
    template<typename T>
    inline Variable::Variable(T v, Z3_context ctx):m_ctx(ctx), m_ast(NULL), bitn(sizeof(T) * 8) { *(T*)m_bytes = v; };//G
	template<typename T>
	inline Variable::Variable(T v, Z3_context ctx, UShort size) :m_ctx(ctx), bitn(size), m_ast(NULL) { *(T*)m_bytes = v;  };//G
	


	inline Variable::Variable(Z3_context ctx, Z3_ast ast, UShort n) ://main
		m_ctx(ctx),
		m_ast(ast),
		bitn(n)
	{
		vassert(ast);
		Z3_inc_ref(ctx, ast);
	}
	inline Variable::Variable(Z3_context ctx, Z3_ast ast, Z3_ast delast, UShort n) ://main
		m_ctx(ctx),
		m_ast(ast),
		bitn(n)
	{
		vassert(ast);
		Z3_inc_ref(ctx, ast);
		Z3_dec_ref(ctx, delast);
	}
	inline Variable::Variable(Z3_context ctx, Z3_ast ast, Z3_context dectx, Z3_ast delast, UShort n) ://main
		m_ctx(ctx),
		m_ast(ast),
		bitn(n)
	{
		vassert(ast);
		Z3_inc_ref(ctx, ast);
		Z3_dec_ref(dectx, delast);
	}
	inline Variable::Variable(Z3_context ctx, Bool no_inc_ref, Z3_ast ast, UShort n) ://main
		m_ctx(ctx),
		m_ast(ast),
		bitn(n)
	{
		vassert(ast);
	}
	inline Variable::Variable(Z3_context ctx, Z3_ast ast) : 
		m_ctx(ctx),
		m_ast(ast)
	{
		vassert(ast);
		Z3_inc_ref(ctx, ast); 
		bitn = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast));
	}
	
	inline Variable::Variable(Z3_context ctx, Bool no_inc_ref, Z3_ast ast) :
		m_ctx(ctx),
		m_ast(ast),
		bitn(Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast)))
	{
		vassert(ast);
	}

	inline Variable::Variable(expr &exp, UShort n) : Variable(exp.ctx(), exp, n) {}
	inline Variable::Variable(expr &exp) : Variable(exp.ctx(), exp) {}


	template<typename T>
	inline Variable::operator T() const { return *(T*)(m_bytes); }
	
	inline Variable::operator Z3_ast() const {
		if (real()) {
			Z3_ast r_ast;
			Z3_sort zsort = Z3_mk_bv_sort(m_ctx, bitn);
			Z3_inc_ref(m_ctx, reinterpret_cast<Z3_ast>(zsort));
			r_ast = Z3_mk_unsigned_int64(m_ctx, *this, zsort);
			Z3_inc_ref(m_ctx, r_ast);
			Z3_dec_ref(m_ctx, reinterpret_cast<Z3_ast>(zsort));
			if (bitn > 64) {
				for (int con = 1; con < (bitn >> 6); con++) {
					zsort = Z3_mk_bv_sort(m_ctx, 64);
					Z3_inc_ref(m_ctx, reinterpret_cast<Z3_ast>(zsort));
					auto new_ast = Z3_mk_unsigned_int64(m_ctx, ((ULong*)m_bytes)[con], zsort);
					Z3_inc_ref(m_ctx, new_ast);
					Z3_dec_ref(m_ctx, reinterpret_cast<Z3_ast>(zsort));
					auto concat_ast = Z3_mk_concat(m_ctx, new_ast, r_ast);
					Z3_inc_ref(m_ctx, concat_ast);
					Z3_dec_ref(m_ctx, new_ast);
					Z3_dec_ref(m_ctx, r_ast);
					r_ast = concat_ast;
				}
			}
			*(Z3_ast*)(void *)(&this->m_ast) = r_ast;//ÈÆ¹ýconst
		}; 
		return m_ast;
	}
	inline Variable::operator void *() const { return (void *)m_bytes; }

	template<typename T, UChar offset>
	inline T Variable::get() { vassert(real()); return *(T*)(m_bytes + offset); }

	inline Variable Variable::bv2fpa(sort &s) { return Variable(m_ctx, Z3_mk_fpa_to_fp_bv(m_ctx, *this, s), bitn); };
	
	inline Variable Variable::fpa2bv() { return Variable(m_ctx, Z3_mk_fpa_to_ieee_bv(m_ctx, *this), bitn); };

	inline Variable Variable::integer2fp_bv(z3::sort &rm, sort &fpa_sort) { return Variable(m_ctx, Z3_mk_fpa_to_fp_signed(m_ctx, rm, *this, fpa_sort), bitn).fpa2bv(); };
	inline Variable Variable::uinteger2fp_bv(z3::sort &rm, sort &fpa_sort) { return Variable(m_ctx, Z3_mk_fpa_to_fp_unsigned(m_ctx, rm, *this, fpa_sort), bitn).fpa2bv(); };

	inline Variable Variable::fp2integer_bv(z3::sort &rm, sort &fpa_sort) { return Variable(m_ctx, Z3_mk_fpa_to_sbv(m_ctx, rm, bv2fpa(fpa_sort), bitn)); };
	inline Variable Variable::fp2uinteger_bv(z3::sort &rm, sort &fpa_sort) { return Variable(m_ctx, Z3_mk_fpa_to_ubv(m_ctx, rm, bv2fpa(fpa_sort), bitn)); };

	inline Z3_sort_kind Variable::sort_kind() const { return Z3_get_sort_kind(m_ctx, Z3_get_sort(m_ctx, m_ast)); }

	inline Z3_ast_kind Variable::ast_kind()const { return Z3_get_ast_kind(m_ctx, m_ast); }


	inline Variable Variable::simplify()
	{
		if (symbolic()) {
			Z3_ast simp = Z3_simplify(m_ctx, m_ast);
			if (Z3_get_ast_kind(m_ctx, simp) == Z3_NUMERAL_AST) {
				if (bitn <= 64) {
					uint64_t TMP;
					Z3_get_numeral_uint64(m_ctx, simp, &TMP);
					return Variable(TMP, m_ctx, bitn);
				}
				else {
					__m128i buff;
					intString2bytes((unsigned char*)Z3_get_numeral_string(m_ctx, m_ast), 32, (char*)&buff);
					return Variable(buff, m_ctx, bitn);
				}
			}
			return Variable(m_ctx, simp, bitn);
		}
		return *this;
		
	}

	inline Variable Variable::Split(UChar size, UInt low)
	{
		if (real()) {
			return Variable(GET32(m_bytes + low), m_ctx, size << 3);
		}
		else {
			return Variable(m_ctx, Z3_mk_extract(m_ctx, ((low + size) << 3) - 1, low << 3, m_ast), size << 3);
		}
	}

	inline Variable Variable::Concat(Variable & low)
	{
		vassert((low.bitn + bitn) <= 256);
		if (real() && low.real()) {
			__m256i re = low;
			memcpy(&re.m256i_u8[(low.bitn>>3)], this->m_bytes, (this->bitn) >> 3);
			return Variable(re, m_ctx, low.bitn + bitn);
		}
		else {
			return Variable(m_ctx, Z3_mk_concat(m_ctx, *this, low), low.bitn + bitn);
		}
	}
template<int hi,int lo>
	inline Variable Variable::extract()
	{
		if (m_ast)
			return Variable(m_ctx, Z3_mk_extract(m_ctx, hi, lo, m_ast), hi - lo + 1);
		if (lo % 8)
			return Variable(m_ctx, Z3_mk_extract(m_ctx, hi, lo, *this), hi - lo + 1).simplify();
		return Variable(_mm256_srli_si256(*this, lo >> 3), m_ctx, hi - lo + 1);
	}

	inline Variable Variable::extract(int hi, int lo)
	{
		if (m_ast)
			return Variable(m_ctx, Z3_mk_extract(m_ctx, hi, lo, m_ast), hi - lo + 1);
		if(lo%8)
			return Variable(m_ctx, Z3_mk_extract(m_ctx, hi, lo, *this), hi - lo + 1).simplify();
		return Variable(GET32(&m_bytes[lo >> 3]), m_ctx, hi - lo + 1);
	}
	inline Variable Variable::zext( int i) { 
		if (i < 0) 
			return extract(bitn + i-1, 0);
		if (m_ast) {
			return Variable(m_ctx, Z3_mk_zero_ext(m_ctx, i, m_ast), bitn + i);
		}
		if (bitn % 8)
			return Variable(m_ctx, Z3_mk_zero_ext(m_ctx, i, *this), bitn + i).simplify();
		auto tmp = GET32(m_bytes);
		memset(&tmp.m256i_i8[(bitn - 1) >> 3], 0ul, i >> 3);
		return Variable(tmp, m_ctx, bitn + i);
	}
	inline Variable Variable::sext( int i) {
		if (i < 0)
			return extract(bitn + i-1, 0);
		if (m_ast) {
			return Variable(m_ctx, Z3_mk_sign_ext(m_ctx, i, m_ast), bitn + i);
		}
		if(bitn%8)
			return Variable(m_ctx, Z3_mk_sign_ext(m_ctx, i, *this), bitn + i).simplify();
		
		auto tmp = GET32(m_bytes);
		if ((m_bytes[(bitn-1) >> 3] >> (7)) & 1) {
			memset(&tmp.m256i_i8[bitn >> 3], -1ul, i >> 3);
		}else{
			memset(&tmp.m256i_i8[bitn >> 3], 0ul, i >> 3);
		}
		return Variable(tmp, m_ctx, bitn + i);
	}
	inline int Variable::real() const { return m_ast == NULL; }
	inline int Variable::real() { return m_ast == NULL; }
	inline int Variable::symbolic() const { return m_ast != NULL; }
	inline int Variable::symbolic() { return m_ast != NULL; }

inline void Variable::operator=(Variable & a)
{
	Variable::~Variable();
	bitn = a.bitn;
	m_ctx = a.m_ctx;
	if (a.real()) {
		m_ast = NULL;
		MV32(m_bytes, a.m_bytes);
	}
	else {
		m_ast = a.m_ast;
		Z3_inc_ref(m_ctx, m_ast);
	}
}
inline Variable::Variable(const Variable &a)
	:bitn(a.bitn), 
	m_ctx(a.m_ctx) 
{
	if (a.real()) {
		m_ast = NULL;
		MV32(m_bytes, a.m_bytes);
	}
	else {
		m_ast = a.m_ast;
		Z3_inc_ref(m_ctx, m_ast);
	}
}

inline Variable::Variable(Z3_context ctx, IRConst *con):m_ctx(ctx),m_ast(NULL)
{
	switch (con->tag) {
	case Ico_U1:   bitn = 1;  SET1(m_bytes, con->Ico.U1); break;
	case Ico_U8:   bitn = 8;  SET1(m_bytes, con->Ico.U8); break;
	case Ico_U16:  bitn = 16; SET2(m_bytes, con->Ico.U16); break;
	case Ico_U32:  bitn = 32; SET4(m_bytes, con->Ico.U32); break;
	case Ico_U64:  bitn = 64; SET8(m_bytes, con->Ico.U64); break;
	case Ico_F32:  bitn = 32; SET4(m_bytes, con->Ico.U32); break;
	case Ico_F32i: bitn = 32; SET4(m_bytes, con->Ico.U32); break;
	case Ico_F64:  bitn = 64; SET8(m_bytes, con->Ico.U64); break;
	case Ico_F64i: bitn = 64; SET8(m_bytes, con->Ico.U64); break;
	case Ico_V128: bitn = 128; SET16(m_bytes, _mm_set1_epi16(con->Ico.V128)); break;
	case Ico_V256: bitn = 256; SET32(m_bytes, _mm256_set1_epi32(con->Ico.V256)); break;
	default: vpanic("tIRConst");
	}
}
inline Variable::operator std::string() {
	std::string str;
	char buff[200];
	if (real()) {
		switch (bitn) {
		case 1:   snprintf(buff, sizeof(buff), " BV%d( %02x )", bitn, ((real_union*)m_bytes)->u8); break;
		case 8:   snprintf(buff, sizeof(buff), " BV%d( %02x )", bitn, ((real_union*)m_bytes)->u8); break;
		case 16:  snprintf(buff, sizeof(buff), " BV%d( %04x )", bitn, ((real_union*)m_bytes)->u16); break;
		case 32:  snprintf(buff, sizeof(buff), " BV%d( %08x )", bitn, ((real_union*)m_bytes)->u32); break;
		case 64:  snprintf(buff, sizeof(buff), " BV%d( %016llx )", bitn, ((real_union*)m_bytes)->u64); break;
		case 128: snprintf(buff, sizeof(buff), " BV%d( %016llx %016llx )", bitn, ((real_union*)m_bytes)->m128.m128_u64[1], ((real_union*)m_bytes)->m128.m128_u64[0]); break;
		case 256: snprintf(buff, sizeof(buff), " BV%d( %016llx %016llx %016llx %016llx )", bitn, ((real_union*)m_bytes)->m256i.m256i_u64[3], ((real_union*)m_bytes)->m256i.m256i_u64[2], ((real_union*)m_bytes)->m256i.m256i_u64[1], ((real_union*)m_bytes)->m256i.m256i_u64[0]); break;
		default:
			vex_printf("\nbitn = 0x%x\n", (UInt)bitn);
			vpanic("bitn err\n");;
		}
	}
	else {
		snprintf(buff, sizeof(buff), " BS%d < \\%llx  >" , bitn , m_ast) ;
		//vex_printf(" BVS %d < \\%s/ >  ", bitn, Z3_ast_to_string(m_ctx, m_ast));
	}

	str.assign(buff);
	return str;
}

inline Variable::~Variable() { if (m_ast) { Z3_dec_ref(m_ctx, m_ast); } };


inline Variable ite(Variable const & a, Variable const & b, Variable const & c) { 
	if (a.real()) {
		return (((UChar)a) & 1) ? b : c;
	}
	return Variable(a, Z3_mk_ite(a, a.toBool(), b, c), b.bitn);
}

inline std::ostream & operator<<(std::ostream & out, Variable & n) {
	std::string child_str = n;
	return out << child_str;
}


inline Variable Variable::mkFalse() const {
	return Variable(m_ctx, Z3_mk_false(m_ctx), 1);
}
inline Variable Variable::mkTrue() const {
	return Variable(m_ctx, Z3_mk_true(m_ctx), 1);
}

inline Variable Variable::toBool() const
{
	vassert(bitn == 1);
	if (m_ast) {
		if (sort_kind() == Z3_BOOL_SORT) {
			return *this;
		}
		else {
			return Variable(m_ctx, Z3_mk_eq(m_ctx, m_ast, Variable(1, m_ctx, 1)), 1);
		}
	}
	if ((UChar)(*this) & 1) {
		return mkTrue();
	}
	return mkFalse();
}

inline Variable Variable::boolXor(Variable &b) {
	if (b.real()) {
		if ((UChar)b & 1) 
			return *this == mkFalse();
		return  *this;
	}
	return  Variable(m_ctx, Z3_mk_xor(m_ctx, *this, b), 1);
}

inline Variable Variable::translate(Z3_context target_ctx)
{
	if (real()) {
		return  Variable( GET32(m_bytes), target_ctx, bitn);
	}
	return Variable(target_ctx, Z3_translate(m_ctx, *this, target_ctx), bitn);
}

inline Bool Variable::is_bool()
{
	vassert(bitn == 1);
	if (symbolic()) {
		return Z3_get_sort_kind(m_ctx, Z3_get_sort(m_ctx, m_ast))== Z3_BOOL_SORT;
	}
	return True;
}


#endif // !ASDREFGSER