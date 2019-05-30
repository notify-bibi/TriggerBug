#pragma once
#ifndef _Vns_H_
#define _Vns_H_
using namespace z3;


typedef enum :UChar {
	REAL		= 0b00,
	REAL_BCKAST = 0b01,
	SYMB		= 0b11,
}V_Kind;

class Vns{
	template <int maxlength>
	friend class Register;
	friend class State;
public:
	__declspec(align(32)) union _pack {
		unsigned char		bit;
		float               f32;
		double              d64;
		__int8              i8;
		__int16             i16;
		__int32             i32;
		__int64             i64;
		unsigned __int8     u8;
		unsigned __int16    u16;
		unsigned __int32    u32;
		unsigned __int64    u64;
		__m64               m64;
		__m128              m128;
		__m128i             m128i;
		__m128d             m128d;
		__m256              m256;
		__m256i             m256i;
		__m256d             m256d;

		unsigned char		_bit[32];
		float               _f32[8];
		double              _d64[4];
		__int8              _i8[32];
		__int16             _i16[16];
		__int32             _i32[8];
		__int64             _i64[4];
		unsigned __int8     _u8[32];
		unsigned __int16    _u16[16];
		unsigned __int32    _u32[8];
		unsigned __int64    _u64[4];
		__m64               _m64[4];
		__m128              _m128[2];
		__m128i             _m128i[2];
		__m128d             _m128d[2];
	}pack;
	Z3_context m_ctx;
	Z3_ast m_ast;
	V_Kind m_kind;
	UShort bitn;

	inline Vns();
	template<typename T>
	inline Vns(Z3_context ctx,		T   v);
	template<typename T>
	inline Vns(Z3_context ctx,		T   v, UShort size);
	inline Vns(Z3_context ctx, Z3_ast ast);
	inline Vns(Z3_context ctx, Z3_ast ast, UShort    n);//main
	inline Vns(expr const &exp, UShort n);//S
	inline Vns(Z3_context ctx,  IRConst *con);
	inline Vns(Z3_context ctx, bool tf);

	template<typename T>
	inline void operator = (const T &a);
	inline Vns(const Vns &a);
	inline void operator = (const Vns &a);
	inline Vns(const expr &a);
	inline void operator = (const expr &a);

	template<typename T>
	inline operator T() const;
	inline operator Z3_context() const;
	inline operator Z3_ast() const;
	inline operator Z3_sort() const;
	inline operator std::string() const;

	template<typename T, UChar offset>
	inline T		get();

	inline Z3_ast		ast(Z3_context ctx) const;
	inline int			real() const;
	inline int			symbolic() const;
	inline Bool			is_bool() const;
	inline Z3_sort_kind sort_kind() const;
	inline Z3_ast_kind	ast_kind() const;

	inline Vns simplify();
	inline Vns bv2fpa(sort &s);
	inline Vns fpa2bv();
	inline Vns integer2fp_bv(z3::sort &rm, sort &fpa_sort);
	inline Vns fp2integer_bv(z3::sort &rm, sort &fpa_sort);
	inline Vns uinteger2fp_bv(z3::sort &rm, sort &fpa_sort);
	inline Vns fp2uinteger_bv(z3::sort &rm, sort &fpa_sort);
	inline Vns fp2fp_bv(z3::sort &rm, sort &fpa_sortsort, sort &to_fpa_sort, UInt to_size);
	
	inline Vns Split(UChar size, UInt low);
	template<int hi, int lo>
	inline Vns extract() const;
	inline Vns extract(int hi, int lo) const;
	inline Vns Concat(Vns &low) const;
	inline Vns zext(int i) const;
	inline Vns sext(int i) const;

	inline Vns toZ3Bool() const;
	inline Vns boolXor(Vns &b);
	inline Vns translate(Z3_context m_ctx);
	inline Vns mkFalse();
	inline Vns mkTrue();
#define VnsOperator_eq(op)				   \
	template<typename T>				   \
	inline void operator##op##=(T v) {	   \
		*this = (*this) op (v);			   \
	}
	VnsOperator_eq(/ );
	VnsOperator_eq(%);
	VnsOperator_eq(*);
	VnsOperator_eq(-);
	VnsOperator_eq(+);
	VnsOperator_eq(| );
	VnsOperator_eq(&);
	VnsOperator_eq(^);
	VnsOperator_eq(>> );
	VnsOperator_eq(<< );
#undef VnsOperator_eq
	inline ~Vns();
private:
	inline operator expr()  = delete;
	inline operator expr&()  = delete;
	inline operator expr() const = delete;
	inline operator expr&() const = delete;
	inline operator const expr() = delete;
	inline operator const expr &() = delete;
};

#define Macrro_integer(Macrro, op, issigned, opname)				\
Macrro(op, unsigned int,	issigned, ##opname);					\
Macrro(op, unsigned long,	issigned, ##opname);					\
Macrro(op, unsigned long long,	issigned, ##opname);				\
Macrro(op, int,	issigned, ##opname);								\
Macrro(op, long,	issigned, ##opname);							\
Macrro(op, long long,	issigned, ##opname);						\



#define VnsOperator_integer(op, T, issigned)																															\
static inline Vns operator##op##(Vns const &a, T b) {																													\
	if(a.bitn==(sizeof(T)<<3))	return a op Vns(a, b);																													\
	return (a.bitn>(sizeof(T)<<3))? a op Vns(a, b).##issigned##ext(a.bitn-(sizeof(T)<<3)) : a.##issigned##ext((sizeof(T)<<3)-a.bitn) op Vns(a, b);						\
}																																										\
static inline Vns operator##op##(T a, Vns const &b) {																													\
	if(b.bitn==(sizeof(T)<<3))	return Vns(b, a) op b;																													\
	return (b.bitn>(sizeof(T)<<3))? Vns(b, a).##issigned##ext(b.bitn - (sizeof(T) << 3)) op b : Vns(b, a) op b.##issigned##ext((sizeof(T) << 3) - b.bitn);				\
}																																										


#define VnsOperator_integer_opname(op, T, issigned, opname)																												\
static inline Vns opname(Vns const &a, T b) {																															\
	if(a.bitn==(sizeof(T)<<3))	return a op Vns(a, b);																													\
	return (a.bitn>(sizeof(T)<<3))? opname(a , Vns(a, b).##issigned##ext(a.bitn-(sizeof(T)<<3))) :opname( a.##issigned##ext((sizeof(T)<<3)-a.bitn) , Vns(a, b));		\
}																																										\
static inline Vns opname(T a, Vns const &b) {																															\
	if(b.bitn==(sizeof(T)<<3))	return Vns(b, a) op b;																													\
	return (b.bitn>(sizeof(T)<<3))? opname(Vns(b, a).##issigned##ext(b.bitn - (sizeof(T) << 3)) , b) : opname(Vns(b, a) , b.##issigned##ext((sizeof(T) << 3) - b.bitn));\
}


#define VnsOperator_bitwishe(op, z3op, issigned) 												\
static inline Vns operator##op##(Vns const &a, Vns const &b) {									\
	if(a.real()&&b.real()){																		\
		switch(a.bitn){																			\
		case 8: return Vns(a, (issigned##Char)a  op (issigned##Char)b, 8);						\
		case 16:return Vns(a, (issigned##Short)a  op(issigned##Short)b, 16);					\
		case 32:return Vns(a, (issigned##Int)a  op(issigned##Int)b, 32);						\
		case 64:return Vns(a, (issigned##Long)a  op (issigned##Long)b, 64);						\
		default:return Vns(a, z3op(a, a, b), a.bitn).simplify();								\
		}																						\
	}																							\
	else {																						\
		return Vns(a, z3op(a, a, b), a.bitn);													\
	}																							\
};																																		


#define VnsOperator_bitwishe_flag(op, z3op, issigned) 											\
static inline Vns operator##op##(Vns const &a, Vns const &b) {									\
	if(a.real()&&b.real()){																		\
		switch(a.bitn){																			\
		case 8: return Vns(a, (issigned##Char)a  op (issigned##Char)b, 1);						\
		case 16:return Vns(a, (issigned##Short)a  op(issigned##Short)b, 1);						\
		case 32:return Vns(a, (issigned##Int)a  op(issigned##Int)b, 1);							\
		case 64:return Vns(a, (issigned##Long)a  op (issigned##Long)b, 1);						\
		default:return Vns(a, z3op(a, a, b), 1).simplify();										\
		}																						\
	}																							\
	else {																						\
		return Vns(a, z3op(a, a, b), 1);														\
	}																							\
};																																		



#define VnsOperator_bitwishe_flag_opname(opname, op, z3op, issigned) 							\
static inline Vns opname(Vns const &a, Vns const &b) {											\
	if(a.real()&&b.real()){																		\
		switch(a.bitn){																			\
		case 8: return Vns(a, (issigned##Char)a  op (issigned##Char)b, 1);						\
		case 16:return Vns(a, (issigned##Short)a  op(issigned##Short)b, 1);						\
		case 32:return Vns(a, (issigned##Int)a  op(issigned##Int)b, 1);							\
		case 64:return Vns(a, (issigned##Long)a  op (issigned##Long)b, 1);						\
		default:return Vns(a, z3op(a, a, b), 1).simplify();										\
		}																						\
	}																							\
	else {																						\
		return Vns(a, z3op(a, a, b), 1);														\
	}																							\
};																																		



VnsOperator_bitwishe(/ , Z3_mk_bvudiv, U);
Macrro_integer(VnsOperator_integer, / , z);
VnsOperator_bitwishe(%, Z3_mk_bvsmod, U);
Macrro_integer(VnsOperator_integer, %, z);
VnsOperator_bitwishe(*, Z3_mk_bvmul, U);
Macrro_integer(VnsOperator_integer, *, z);
VnsOperator_bitwishe(-, Z3_mk_bvsub, U);
Macrro_integer(VnsOperator_integer, -, z);
VnsOperator_bitwishe(+, Z3_mk_bvadd, U);
Macrro_integer(VnsOperator_integer, +, z);
VnsOperator_bitwishe(| , Z3_mk_bvor, U);
Macrro_integer(VnsOperator_integer, | , z);
VnsOperator_bitwishe(&, Z3_mk_bvand, U);
Macrro_integer(VnsOperator_integer, &, z);

VnsOperator_bitwishe(>> , Z3_mk_bvlshr, U);
Macrro_integer(VnsOperator_integer, >> , z);
VnsOperator_bitwishe(<< , Z3_mk_bvshl, U);
Macrro_integer(VnsOperator_integer, << , z);
VnsOperator_bitwishe(^, Z3_mk_bvxor, U);
Macrro_integer(VnsOperator_integer, ^, z);


VnsOperator_bitwishe_flag( <= , Z3_mk_bvule, U);
Macrro_integer(VnsOperator_integer, <= , z);
VnsOperator_bitwishe_flag( <  , Z3_mk_bvult, U);
Macrro_integer(VnsOperator_integer, < , z);
VnsOperator_bitwishe_flag( >= , Z3_mk_bvuge, U);
Macrro_integer(VnsOperator_integer, >= , z);
VnsOperator_bitwishe_flag( >  , Z3_mk_bvugt, U);
Macrro_integer(VnsOperator_integer, > , z);
VnsOperator_bitwishe_flag( == , Z3_mk_eq   , U);
Macrro_integer(VnsOperator_integer, == , z);
VnsOperator_bitwishe_flag( != , Z3_mk_neq  , U);
Macrro_integer(VnsOperator_integer, != , z);

VnsOperator_bitwishe_flag_opname( le ,<= , Z3_mk_bvsle, S);
Macrro_integer(VnsOperator_integer_opname, <= , s, le);
VnsOperator_bitwishe_flag_opname( lt ,<  , Z3_mk_bvslt, S);
Macrro_integer(VnsOperator_integer_opname, < , s, lt);
VnsOperator_bitwishe_flag_opname( ge ,>= , Z3_mk_bvsge, S);
Macrro_integer(VnsOperator_integer_opname, >= , s, ge);
VnsOperator_bitwishe_flag_opname( gt ,>  , Z3_mk_bvsgt, S);
Macrro_integer(VnsOperator_integer_opname, > , s, gt);


inline Vns operator!(Vns const &a) {
	if (a.real()) {
		return Vns(a, !(UChar)(a));
	}
	return Vns(a, Z3_mk_not(a, a), 1);
}
inline Vns operator-(Vns const &a) {
	if (a.real()) {
		switch (a.bitn) {
		case 8: return Vns(a, -(SChar)(a), 8);
		case 16:return Vns(a, -(SShort)(a), 16);
		case 32:return Vns(a, -(SInt)(a), 32);
		case 64:return Vns(a, -(SLong)(a), 64);
		default:return Vns(a, Z3_mk_bvneg(a, a), a.bitn).simplify();
		}
	}
	return Vns(a, Z3_mk_bvneg(a, a), a.bitn);
}

inline Vns operator~(Vns const &a) {
	if (a.real()) {
		switch (a.bitn) {
		case 8: return Vns(a, ~(SChar)(a), 8);
		case 16:return Vns(a, ~(SShort)(a), 16);
		case 32:return Vns(a, ~(SInt)(a), 32);
		case 64:return Vns(a, ~(SLong)(a), 64);
		default:return Vns(a, Z3_mk_bvnot(a, a), a.bitn).simplify();
		}
	}
	return Vns(a, Z3_mk_bvnot(a, a), a.bitn);
}



static inline Vns operator||(Vns const &a, Vns const &b) {
	if (a.real()) 
		return (UChar(a)) ? a : b;
	Z3_ast args[2] = { a.toZ3Bool(), b.toZ3Bool() };
	return Vns(a, Z3_mk_or(a, 2, args), 1);
};																				 
static inline Vns operator||(bool a, Vns const &b) {
	return Vns(b, a, 1) || b;													 
};																				 
static inline Vns operator||(Vns const &a,  bool b) {
	return a || Vns(a, b, 1);
};												


static inline Vns operator&&(Vns const &a, Vns const &b) {
	if (a.real()) {
		return (UChar(a)) ? b : a;
	}
	Z3_ast args[2] = { a.toZ3Bool(), b.toZ3Bool() };
	return Vns(a, Z3_mk_and(a, 2, args), 1);
};																				 
static inline Vns operator&&(Vns const &a, bool b) {
	return a && Vns(a, b, 1);													 
};																				 
static inline Vns operator&&(bool a, Vns const &b) {
	return Vns(b, a, 1) && b;													 
};



static inline Vns ite(Vns const & a, Vns const & b, Vns const & c) {
	if (a.real()) {
		if (a.bitn == 1)
			return (((UChar)a) & 1) ? b : c;
		else
			return ((ULong)a & fastMask[a.bitn]) ? b : c;
	}
	return Vns(a, Z3_mk_ite(a, a.toZ3Bool(), b, c), b.bitn);
}

static inline Vns ashr(Vns const &a, Vns const  &b) {
	if(a.real()||b.real()){
		switch (a.bitn) {
		case 8: return Vns(a, (SChar)a >> ((UChar)b), 8);
		case 16:return Vns(a, (SShort)a >> ((UChar)b), 16);
		case 32:return Vns(a, (SInt)a >> ((UChar)b), 32);
		case 64:return Vns(a, (SLong)a >> ((UChar)b), 64);
		default:
			if(a.bitn==b.bitn)
				return Vns(a, Z3_mk_bvashr(a, a, b), a.bitn).simplify();
			else if(a.bitn > b.bitn)
				return Vns(a, Z3_mk_bvashr(a, a, b.zext(a.bitn - b.bitn)), a.bitn).simplify();
			else if (a.bitn < b.bitn)
				return Vns(a, Z3_mk_bvashr(a, a.zext(b.bitn - a.bitn), b), a.bitn).simplify();
		}
	}																
	else {
		if (a.bitn == b.bitn)
			return Vns(a, Z3_mk_bvashr(a, a, b), a.bitn);
		else if (a.bitn > b.bitn)
			return Vns(a, Z3_mk_bvashr(a, a, b.zext(a.bitn - b.bitn)), a.bitn);
		else if (a.bitn < b.bitn)
			return Vns(a, Z3_mk_bvashr(a, a.zext(b.bitn - a.bitn), b), a.bitn);
	}																
}

template<typename T>												
static inline Vns ashr(Vns const &a, T b) {
	return ashr(a, Vns(a, b));
}			

template<typename T>												
static inline Vns ashr(T a, Vns const &b) {
	return  ashr(Vns(b, a), b);
}							

static inline std::ostream & operator<<(std::ostream & out, Vns & n) {
	std::string child_str = n;
	return out << child_str;
}

#undef VnsOperator_bitwishe 
#undef VnsOperator_bitwishe_flag
#undef VnsOperator_integer 
#undef VnsOperator_bitwishe_flag_opname 
#undef VnsOperator_integer_opname
#undef Macrro_integer
#undef VnsOperator_eq


#endif // _Vns_H_