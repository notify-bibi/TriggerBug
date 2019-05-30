#pragma once
#ifndef _Vns_
#define _Vns_

static inline void intString2bytes(unsigned char *bytesbuff, size_t n, const char * int_str) {
	PyObject *value = PyLong_FromString(int_str, 0, 10);
	_PyLong_AsByteArray((PyLongObject*)value, bytesbuff, n, 1, 0);
}

using namespace z3;

	inline Vns::Vns() : m_kind(REAL) {};//G
	template<typename T>
	inline Vns::Vns(Z3_context ctx, T v) :
		m_ctx(ctx),
		m_kind(REAL),
		bitn(sizeof(T) << 3) 
	{ 
		*(T*)&this->pack = v; 
	};

	template<typename T>
	inline Vns::Vns(Z3_context ctx, T v, UShort size ) :
		m_ctx(ctx),
		m_kind(REAL), 
		bitn(size) 
	{
		*(T*)&this->pack = v;
	};

	inline Vns::Vns(Z3_context ctx, Z3_ast ast) :
		m_ctx(ctx),
		m_ast(ast),
		m_kind(SYMB)
	{
		Z3_inc_ref(ctx, ast);
		vassert(ast&&sort_kind()== Z3_BV_SORT);
		bitn = Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, m_ast));
	}

	inline Vns::Vns(Z3_context ctx, Z3_ast ast, UShort n) ://main
		m_ctx(ctx),
		m_ast(ast),
		m_kind(SYMB),
		bitn(n)
	{
		vassert(ast);
		Z3_inc_ref(ctx, ast);
	}

	inline Vns::Vns(expr const &exp, UShort n) : Vns(exp.ctx(), exp, n) {};


	inline Vns::Vns(Z3_context ctx, IRConst *con) :
		m_ctx(ctx),
		m_kind(REAL)
	{
		switch (con->tag) {
		case Ico_U1:   bitn = 1;  this->pack.bit = con->Ico.U1; break;
		case Ico_U8:   bitn = 8;  SET1(&this->pack, con->Ico.U8); break;
		case Ico_U16:  bitn = 16; SET2(&this->pack, con->Ico.U16); break;
		case Ico_U32:  bitn = 32; SET4(&this->pack, con->Ico.U32); break;
		case Ico_U64:  bitn = 64; SET8(&this->pack, con->Ico.U64); break;
		case Ico_F32:  bitn = 32; SET4(&this->pack, con->Ico.U32); break;
		case Ico_F32i: bitn = 32; SET4(&this->pack, con->Ico.U32); break;
		case Ico_F64:  bitn = 64; SET8(&this->pack, con->Ico.U64); break;
		case Ico_F64i: bitn = 64; SET8(&this->pack, con->Ico.U64); break;
		case Ico_V128: bitn = 128; SET16(&this->pack, _mm_set1_epi16(con->Ico.V128)); break;
		case Ico_V256: bitn = 256; SET32(&this->pack, _mm256_set1_epi32(con->Ico.V256)); break;
		default: vpanic("tIRConst");
		}
	}

	inline Vns::Vns(Z3_context ctx, bool tf) :Vns(ctx, tf, 1) {};

	template<typename T>
	inline void Vns::operator = (const T &a)
	{
		Vns::~Vns();
		*(T*)&this->pack = a;
		bitn = sizeof(a) << 3;
		m_kind = REAL;
	}

	inline Vns::Vns(const Vns &a):
		m_ctx(a)
	{
		if (a.m_kind == SYMB) {
			m_ast = a.m_ast;
			Z3_inc_ref(m_ctx, m_ast);
		}
		else {
			this->pack = a.pack;
		}
		bitn = a.bitn;
		m_kind = a.m_kind;
	}

	inline void Vns::operator=(const Vns & a)
	{
		Vns::~Vns();
		m_ctx = a;
		if (a.m_kind == SYMB) {
			m_ast = a.m_ast;
			Z3_inc_ref(m_ctx, m_ast);
		}
		else {
			this->pack = a.pack;
		}
		bitn = a.bitn;
		m_kind = a.m_kind;
	}


	inline Vns::Vns(const expr &a):
		m_ctx(a.ctx())
	{
		switch (Z3_get_sort_kind(m_ctx, Z3_get_sort(m_ctx, a))) {
		case	Z3_BOOL_SORT:
			bitn = 1;
			m_ast = a;
			Z3_inc_ref(m_ctx, m_ast);
			break;
		case	Z3_BV_SORT:
			m_ast = a;
			bitn = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast));
			Z3_inc_ref(m_ctx, m_ast);
			break;
		case	Z3_FLOATING_POINT_SORT:
			m_ast = Z3_mk_fpa_to_ieee_bv(m_ctx, m_ast);
			bitn = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast));
			Z3_inc_ref(m_ctx, m_ast);
			break;
		default: vpanic("un know");
		}
		m_kind = SYMB;
	}

	inline void Vns::operator=(const expr &a) 
	{
		Vns::~Vns();
		m_ctx = a.ctx();
		switch (sort_kind()) {
		case	Z3_BOOL_SORT:
			bitn = 1;
			m_ast = a;
			Z3_inc_ref(m_ctx, m_ast);
			break;
		case	Z3_BV_SORT:
			m_ast = a;
			bitn = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast));
			Z3_inc_ref(m_ctx, m_ast);
			break;
		case	Z3_FLOATING_POINT_SORT:
			m_ast = Z3_mk_fpa_to_ieee_bv(m_ctx, m_ast);
			bitn = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast));
			Z3_inc_ref(m_ctx, m_ast);
			break;
		default: vpanic("un know");
		}
		m_kind = SYMB;
	}

	template<typename T>
	inline Vns::operator T() const { 
		return *(T*)(&this->pack); 
	}

	inline Vns::operator Z3_context() const { return m_ctx; }

	inline Vns::operator Z3_ast() const {
		if (m_kind == REAL) {
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
					auto new_ast = Z3_mk_unsigned_int64(m_ctx, this->pack._i64[con], zsort);
					Z3_inc_ref(m_ctx, new_ast);
					Z3_dec_ref(m_ctx, reinterpret_cast<Z3_ast>(zsort));
					auto concat_ast = Z3_mk_concat(m_ctx, new_ast, r_ast);
					Z3_inc_ref(m_ctx, concat_ast);
					Z3_dec_ref(m_ctx, new_ast);
					Z3_dec_ref(m_ctx, r_ast);
					r_ast = concat_ast;
				}
			}
			//ÈÆ¹ýconst
			*(Z3_ast*)(void *)(&this->m_ast) = r_ast;
			*(V_Kind*)(void *)(&this->m_kind) = REAL_BCKAST;
		};
		return m_ast;
	}

	inline Vns::operator Z3_sort() const { return Z3_get_sort(m_ctx, *this); }

	inline Vns::operator std::string() const {
		std::string str;
		char buff[200];
		if (real()) {
			switch (bitn) {
			case 1:   snprintf(buff, sizeof(buff), " BV%d( %02x )", bitn, this->pack.bit); break;
			case 8:   snprintf(buff, sizeof(buff), " BV%d( %02x )", bitn, this->pack.u8); break;
			case 16:  snprintf(buff, sizeof(buff), " BV%d( %04x )", bitn, this->pack.u16); break;
			case 32:  snprintf(buff, sizeof(buff), " BV%d( %08x )", bitn, this->pack.u32); break;
			case 64:  snprintf(buff, sizeof(buff), " BV%d( %016llx )", bitn, this->pack.u64); break;
			case 128: snprintf(buff, sizeof(buff), " BV%d( %016llx %016llx )", bitn, this->pack.m128.m128_u64[1], this->pack.m128.m128_u64[0]); break;
			case 256: snprintf(buff, sizeof(buff), " BV%d( %016llx %016llx %016llx %016llx )", bitn, this->pack.m256i.m256i_u64[3], this->pack.m256i.m256i_u64[2], this->pack.m256i.m256i_u64[1], this->pack.m256i.m256i_u64[0]); break;
			default:
				vex_printf("\nbitn = 0x%x\n", (UInt)bitn);
				vpanic("bitn err\n");
			}
		}
		else {
			snprintf(buff, sizeof(buff), " BS%d < \\%llx  >", bitn, m_ast);
			//vex_printf(" BVS %d < \\%s/ >  ", bitn, Z3_ast_to_string(m_ctx, m_ast));
		}
		str.assign(buff);
		return str;
	}

	template<typename T, UChar offset>
	inline T Vns::get() { assert(real()); return *(T*)(((UChar*)&this->pack) + offset); }

	inline Z3_ast Vns::ast(Z3_context ctx) const {
		return (ctx == m_ctx)? *this : Z3_translate(m_ctx, *this, ctx);
	}

	inline int Vns::real() const { return m_kind != SYMB; }

	inline int Vns::symbolic() const { return  m_kind == SYMB; }

	inline Z3_sort_kind Vns::sort_kind() const { return Z3_get_sort_kind(m_ctx, Z3_get_sort(m_ctx, *this)); }

	inline Z3_ast_kind Vns::ast_kind()const { return Z3_get_ast_kind(m_ctx, *this); }

	inline Vns Vns::simplify()
	{
		if (m_kind != SYMB) 
			return *this;
		Z3_ast simp = Z3_simplify(m_ctx, m_ast);
		if (Z3_get_ast_kind(m_ctx, simp) == Z3_NUMERAL_AST) {
			if (bitn <= 64) {
				uint64_t TMP;
				Z3_get_numeral_uint64(m_ctx, simp, &TMP);
				return Vns(m_ctx, TMP, bitn);
			}
			else {
				__m256i buff;
				intString2bytes((unsigned char*)&buff, 32, (char*)Z3_get_numeral_string(m_ctx, simp));
				return Vns(m_ctx, buff, bitn);
			}
		}
		return Vns(m_ctx, simp, bitn);
	}

	inline Vns Vns::bv2fpa(sort &s) { 
		return Vns(m_ctx, Z3_mk_fpa_to_fp_bv(m_ctx, *this, s), bitn);
	};
	
	inline Vns Vns::fpa2bv() {
		return Vns(m_ctx, Z3_mk_fpa_to_ieee_bv(m_ctx, *this), bitn); 
	};

	inline Vns Vns::integer2fp_bv(z3::sort &rm, sort &fpa_sort) { 
		return Vns(m_ctx, Z3_mk_fpa_to_fp_signed(m_ctx, rm, *this, fpa_sort), bitn).fpa2bv();
	};
	inline Vns Vns::uinteger2fp_bv(z3::sort &rm, sort &fpa_sort) {
		return Vns(m_ctx, Z3_mk_fpa_to_fp_unsigned(m_ctx, rm, *this, fpa_sort), bitn).fpa2bv();
	};

	inline Vns Vns::fp2integer_bv(z3::sort &rm, sort &fpa_sort) { 
		return Vns(m_ctx, Z3_mk_fpa_to_sbv(m_ctx, rm, bv2fpa(fpa_sort), bitn));
	};
	inline Vns Vns::fp2uinteger_bv(z3::sort &rm, sort &fpa_sort) {
		return Vns(m_ctx, Z3_mk_fpa_to_ubv(m_ctx, rm, bv2fpa(fpa_sort), bitn)); 
	};

	inline Vns Vns::fp2fp_bv(z3::sort &rm, sort &fpa_sort, sort &to_fpa_sort, UInt to_size) {
		return Vns(m_ctx, Z3_mk_fpa_to_fp_float(m_ctx, rm, bv2fpa(fpa_sort), to_fpa_sort), to_size).fpa2bv().simplify();
	};

	/* bitn  */
	inline Vns Vns::Split(UChar size, UInt low)
	{
		if (m_kind == SYMB) {
			return Vns(m_ctx, Z3_mk_extract(m_ctx, low + size - 1, low, m_ast), size);
		}
		else {
			__m256i m32 = GET32(&this->pack._u8[low >> 3]);
			if (low % 8) {
				UChar bytes_n = (size >> 6);
				for (int i = 0; i <= bytes_n; i++) {
					m32.m256i_u64[i] = (m32.m256i_u64[i] >> (low % 8)) | m32.m256i_u64[i + 1] << (64 - low % 8);
				}
			}
			if (m_kind == REAL) {
				return Vns(m_ctx, m32, size);
			}
			else {
				return Vns(m_ctx, m32, size);
			}
		}
	}

	template<int hi,int lo>
	inline Vns Vns::extract() const
	{
		if (m_kind == SYMB) {
			return Vns(m_ctx, Z3_mk_extract(m_ctx, hi, lo, m_ast), (hi - lo + 1));
		}
		else {
			__m256i m32 = GET32(&this->pack._i8[lo >> 3]);
			if (lo & 8) {
				UChar bytes_n = (hi - lo + 1) >> 6;
				for (int i = 0; i <= bytes_n; i++) {
					m32.m256i_u64[i] = (m32.m256i_u64[i] >> (lo & 8)) | m32.m256i_u64[i + 1] << (64 - (lo & 8));
				}
			}
			if (m_kind == REAL) {
				return Vns(m_ctx, m32, (hi - lo + 1));
			}
			else {
				return Vns(m_ctx, m32, (hi - lo + 1));
			}
		}
	}

	inline Vns Vns::extract(int hi, int lo) const
	{
		UShort size = hi - lo + 1;
		if (m_kind == SYMB) {
			return Vns(m_ctx, Z3_mk_extract(m_ctx, hi, lo, m_ast), size);
		}
		else {
			__m256i m32 = GET32(&this->pack._i8[lo >> 3]);
			if (lo % 8) {
				UChar bytes_n = size >> 6;
				for (int i = 0; i <= bytes_n; i++) {
					m32.m256i_u64[i] = (m32.m256i_u64[i] >> (lo & 8)) | m32.m256i_u64[i + 1] << (64 - (lo & 8));
				}
			}
			if (m_kind == REAL) {
				return Vns(m_ctx, m32, size);
			}
			else {
				return Vns(m_ctx, m32, size);
			}
		}
	}

	inline Vns Vns::Concat(Vns & low) const
	{
		vassert((low.bitn + bitn) <= 256);
		if (real() && low.real()) {
			__m256i re = low;
			__m256i m32 = GET32(&this->pack);

			if (low.bitn & 8) {
				re.m256i_u8[low.bitn >> 3] &= fastMask[8 - low.bitn & 7];
				re.m256i_u64[low.bitn >> 3] = (re.m256i_u64[low.bitn >> 3] >> (low.bitn & 8)) | m32.m256i_u64[0] << (64 - (low.bitn & 8));
				UChar bytes_n = bitn >> 6;
				for (int i = 0; i <= bytes_n; i++) {
					m32.m256i_u64[i] = (m32.m256i_u64[i] >> (low.bitn & 8)) | m32.m256i_u64[i + 1] << (64 - (low.bitn & 8));
				}

			}
			memcpy(&re.m256i_u8[(low.bitn >> 3)], &this->pack, (this->bitn) >> 3);
			return Vns(m_ctx, re, low.bitn + bitn);
		}
		else {
			return Vns(m_ctx, Z3_mk_concat(m_ctx, *this, low), low.bitn + bitn);
		}
	}

	inline Vns Vns::zext(int i)const {
		if (i < 0)
			return extract(bitn + i - 1, 0);
		if (m_kind == SYMB) {
		
			return Vns(m_ctx, Z3_mk_zero_ext(m_ctx, i, m_ast), bitn + i);
		}
		auto m32 = GET32(&this->pack);
		if (bitn & 7) {
			m32.m256i_i8[bitn >> 3] &= fastMask[8 - bitn & 7];
		}
		memset(&m32.m256i_i8[((bitn - 1) >> 3) + 1], 0ul, i >> 3);
		if (m_kind == REAL) {
			return Vns(m_ctx, m32, bitn + i);
		}
		else {
			return Vns(m_ctx, m32, bitn + i);
		}
	}
	inline Vns Vns::sext( int i)const {
		if (i < 0)
			return extract(bitn + i-1, 0);
		if (m_kind == SYMB) {
			return Vns(m_ctx, Z3_mk_sign_ext(m_ctx, i, m_ast), bitn + i);
		}
		auto m32 = GET32(&this->pack);
		if ((this->pack._u8[(bitn-1) >> 3] >> (bitn & 7)) & 1) {
			if (bitn & 7) {
				m32.m256i_i8[bitn >> 3] |= fastMaskReverse[8 - (bitn & 7)];
			}
			memset(&m32.m256i_i8[((bitn - 1) >> 3) + 1], -1ul, i >> 3);
		}else{
			if (bitn & 7) {
				m32.m256i_i8[bitn >> 3] &= fastMask[8 - (bitn & 7)];
			}
			memset(&m32.m256i_i8[((bitn - 1) >> 3) + 1], 0ul, i >> 3);
		}
		return Vns(m_ctx, m32, bitn + i);
	}


inline Vns::~Vns() { 
	if (m_kind != REAL) {
		Z3_dec_ref(m_ctx, m_ast);
	}
};


inline Vns Vns::toZ3Bool() const
{
	vassert(bitn == 1);
	if (m_kind == REAL) {
		if ((UChar)(*this)) 
			return Vns(m_ctx, Z3_mk_true(m_ctx), 1);
		else 
			return Vns(m_ctx, Z3_mk_false(m_ctx), 1);
	}
	if (sort_kind() == Z3_BOOL_SORT) {
		return *this;
	}
	else {
		return Vns(m_ctx, Z3_mk_eq(m_ctx, *this, Vns(m_ctx, 1, 1)));
	}
}

inline Vns Vns::boolXor(Vns &b) {
	assert(is_bool());
	if (b.real()) {
		if ((UChar)b) 
			return *this == mkFalse();
		return *this;
	}
	return  Vns(m_ctx, Z3_mk_xor(m_ctx, *this, b), 1);
}

inline Vns Vns::translate(Z3_context target_ctx)
{
	if (real()) {
		return *this;
	}
	return Vns(target_ctx, Z3_translate(m_ctx, *this, target_ctx), bitn);
}

inline Vns Vns::mkFalse() { return Vns(m_ctx, Z3_mk_false(m_ctx), 1); }

inline Vns Vns::mkTrue() { return Vns(m_ctx, Z3_mk_true(m_ctx), 1); }

inline Bool Vns::is_bool() const
{
	vassert(bitn == 1);
	if (m_kind == SYMB) {
		return sort_kind() == Z3_BOOL_SORT;
	}
	return True;
}


#endif // !ASDREFGSER