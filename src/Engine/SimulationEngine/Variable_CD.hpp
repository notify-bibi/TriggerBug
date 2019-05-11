#pragma once
#ifndef VARIABLE_H
#define VARIABLE_H




using namespace z3;


typedef union {
	unsigned char		bit;
	float               f32;
	double              d64;
	unsigned __int64    u64;
	__int8              i8;
	__int16             i16;
	__int32             i32;
	__int64             i64;
	unsigned __int8     u8;
	unsigned __int16    u16;
	unsigned __int32    u32;
	__m64               m64;
	__m128              m128;//单精度浮点数
	__m128i             m128i;//整型
	__m128d             m128d;//双精度浮点数
	__m256              m256;
	__m256i             m256i;
	__m256d             m256d;
}real_union;

class Variable{
	template <int maxlength>
	friend class Register;
	friend class State;
private:
	__declspec(align(32)) UChar m_bytes[32];
	Z3_ast m_ast;
public:
	Z3_context m_ctx;
	UShort bitn;
	inline Variable() ;
	inline Variable(const Variable &a);
	inline void operator = (Variable &a);
	inline void operator = (expr &a);



	template<typename T>
	inline Variable(T v, Z3_context ctx);//R
	template<typename T>
	inline Variable(T v, Z3_context ctx, UShort size);

	inline Variable(Z3_context ctx, IRConst *con);//R
	
	
	inline Variable(Z3_context ctx, Z3_ast ast, UShort n);//main
	inline Variable(Z3_context ctx, Z3_ast ast, Z3_ast delast, UShort n);//main
	inline Variable(Z3_context ctx, Z3_ast ast, Z3_context dectx, Z3_ast delast, UShort n);//main
	inline Variable(Z3_context ctx, Z3_ast ast);

	inline Variable(Z3_context ctx, Bool, Z3_ast ast, UShort n);//main
	inline Variable(Z3_context ctx, Bool, Z3_ast ast);

	inline Variable(expr &exp, UShort n);//S
	inline Variable(expr &exp);//S

	
	inline Variable bv2fpa(sort &s);
	inline Variable fpa2bv();
	inline Variable integer2fp_bv(z3::sort &rm, sort &fpa_sort);
	inline Variable fp2integer_bv(z3::sort &rm, sort &fpa_sort);
	inline Variable uinteger2fp_bv(z3::sort &rm, sort &fpa_sort);
	inline Variable fp2uinteger_bv(z3::sort &rm, sort &fpa_sort);
	inline Variable simplify();
	inline Variable Split(UChar size, UInt low);
	inline int real();
	inline int Variable::real() const;
	inline int symbolic();
	inline int Variable::symbolic() const;
	template<int hi, int lo>
	inline Variable extract();
	inline Variable extract(int hi, int lo);
	inline Variable Concat(Variable &low);
	inline Variable zext( int i);
	inline Variable sext( int i);

	inline Variable mkFalse()const;
	inline Variable mkTrue()const;
	inline Variable toBool() const;
	inline Variable boolXor(Variable &b);
	inline Variable translate(Z3_context m_ctx);
	inline Bool is_bool();
	inline Z3_sort_kind sort_kind() const;
	inline Z3_ast_kind ast_kind() const;

	template<typename T>
	inline operator T() const ;

	inline operator Z3_ast() const;
	inline operator Z3_context() const;
	inline operator void *() const;

	template<typename T, UChar offset>
	inline T get() ;

	inline operator std::string();

	inline ~Variable();

#define VariableOperatorDEF(op)														\
template<typename T>																\
	friend static inline Variable operator##op##(Variable const &a, T b);					\
template<typename T>																\
	friend static inline Variable operator##op##(T a, Variable const &b);					\
	friend static inline Variable operator##op##(Variable const &a, Variable const &b);	\

	VariableOperatorDEF(/)
	VariableOperatorDEF(*)
	VariableOperatorDEF(-)
	VariableOperatorDEF(+)
	VariableOperatorDEF(<=)
	VariableOperatorDEF(< )
	VariableOperatorDEF(>= )
	VariableOperatorDEF(> )
	VariableOperatorDEF(| )
	VariableOperatorDEF(&)
	VariableOperatorDEF(>> )
	VariableOperatorDEF(<< )
	VariableOperatorDEF(|| )
	VariableOperatorDEF(&&)
	VariableOperatorDEF(^)
	VariableOperatorDEF(== )
	VariableOperatorDEF(!= )

};


#define VariableOperator_unsigned(op, z3op, result_bitn) 				\
static inline Variable operator##op##(Variable const &a, Variable const &b) {\
	if(a.real()&&b.real()){												\
		if(a.bitn>64){													\
			return Variable(a, z3op(a, a, b), result_bitn).simplify();	\
		}																\
		return Variable(((ULong)(fastMask[a.bitn] & ((ULong)a)))  op   ((ULong)(fastMask[b.bitn] & ((ULong)b))), a, result_bitn);\
	}																	\
	else {																\
		return Variable(a, z3op(a, a, b), result_bitn);					\
	}																	\
}																		\
template<typename T>													\
static inline Variable operator##op##(Variable const &a, T b) {			\
	return a ##op## Variable(b,a).zext(a.bitn-(sizeof(T)<<3));			\
}																		\
template<typename T>													\
static inline Variable operator##op##(T a, Variable const &b) {			\
	return Variable(a,b).zext(b.bitn-(sizeof(T)<<3)) ##op## b;			\
}

#define VariableOperator_signed(op, z3op, result_bitn) 					\
static inline Variable operator##op##(Variable const &a, Variable const &b) {\
	if(a.real()&&b.real()){												\
		if(a.bitn>64){													\
			return Variable(a, z3op(a, a, b), result_bitn).simplify();	\
		}																\
		return Variable(((Long)(fastMask[a.bitn] & ((ULong)a)))  op   ((Long)(fastMask[b.bitn] & ((ULong)b))), a, result_bitn);\
	}																	\
	else {																\
		return Variable(a, z3op(a, a, b), result_bitn);					\
	}																	\
}																		\
template<typename T>													\
static inline Variable operator##op##(Variable const &a, T b) {			\
	return a ##op## Variable(b,a).sext(a.bitn-(sizeof(T)<<3));			\
}																		\
template<typename T>													\
static inline Variable operator##op##(T a, Variable const &b) {			\
	return Variable(a,b).sext(b.bitn-(sizeof(T)<<3)) ##op## b;			\
}																		



#define VariableOperator_signed_with_opname(opname, op, z3op, result_bitn)\
static inline Variable opname(Variable const &a, Variable const &b) {	\
	if(a.real()&&b.real()){												\
		if(a.bitn>64){													\
			return Variable(a, z3op(a, a, b), result_bitn).simplify();	\
		}																\
		return Variable(((Long)(fastMask[a.bitn] & ((ULong)a)))  op   ((Long)(fastMask[b.bitn] & ((ULong)b))), a, result_bitn);\
	}																	\
	else {																\
		return Variable(a, z3op(a, a, b), result_bitn);					\
	}																	\
}																		\
template<typename T>													\
static inline Variable opname(Variable const &a, T b) {					\
	return opname(a , Variable(b,a).sext(a.bitn-(sizeof(T)<<3)));		\
}																		\
template<typename T>													\
static inline Variable opname(T a, Variable const &b) {					\
	return opname(Variable(a,b).sext(b.bitn-(sizeof(T)<<3)) , b);		\
}																		

#define VariableOperator_bool(op, z3op)									\
static inline Variable operator##op##(Variable const &a, Variable const &b) {\
	if(a.real()&&b.real()){												\
		return Variable((((UChar)a)  op   ((UChar)b)), a, 1);			\
	}																	\
	else {																\
		Z3_ast args[2] = { a.toBool(), b.toBool() };					\
		return Variable(a, z3op(a, 2, args), 1).simplify();				\
	}																	\
}																		\
template<typename T>													\
static inline Variable operator##op##(Variable const &a, T b) {			\
	return a ##op## Variable(b,a,1);									\
}																		\
template<typename T>													\
static inline Variable operator##op##(T a, Variable const &b) {			\
	return Variable(a,b,1) ##op## b;									\
}


VariableOperator_unsigned( / , Z3_mk_bvudiv, a.bitn);
VariableOperator_unsigned( % , Z3_mk_bvsmod, a.bitn);
VariableOperator_unsigned( * , Z3_mk_bvmul , a.bitn);
VariableOperator_unsigned( - , Z3_mk_bvsub , a.bitn);
VariableOperator_unsigned( + , Z3_mk_bvadd , a.bitn);
VariableOperator_unsigned( | , Z3_mk_bvor  , a.bitn);
VariableOperator_unsigned( & , Z3_mk_bvand , a.bitn);

VariableOperator_unsigned( >> , Z3_mk_bvlshr, a.bitn);
VariableOperator_unsigned( << , Z3_mk_bvshl,  a.bitn);
VariableOperator_unsigned( ^  , Z3_mk_bvxor,  a.bitn);


inline Z3_ast Z3_mk_neq(Z3_context ctx, Z3_ast a, Z3_ast b) { return  Z3_mk_not(ctx, Variable(ctx, Z3_mk_eq(ctx, a, b), 1)); };

VariableOperator_bool(|| , Z3_mk_or );
VariableOperator_bool(&& , Z3_mk_and);


VariableOperator_unsigned( <= , Z3_mk_bvule, 1);
VariableOperator_unsigned( <  , Z3_mk_bvult, 1);
VariableOperator_unsigned( >= , Z3_mk_bvuge, 1);
VariableOperator_unsigned( >  , Z3_mk_bvugt, 1);
VariableOperator_unsigned( == , Z3_mk_eq   , 1);
VariableOperator_unsigned( != , Z3_mk_neq  , 1);

VariableOperator_signed_with_opname( le ,<= , Z3_mk_bvsle, 1);
VariableOperator_signed_with_opname( lt ,<  , Z3_mk_bvslt, 1);
VariableOperator_signed_with_opname( ge ,>= , Z3_mk_bvsge, 1);
VariableOperator_signed_with_opname( gt ,>  , Z3_mk_bvsgt, 1);


static inline Variable operator-(Variable  & a) { return Variable(a, Z3_mk_bvneg(a, a), a.bitn); }
static inline Variable operator!(Variable  & a) { return Variable(a, Z3_mk_not(a, a), a.bitn); }
static inline Variable operator~(Variable  & a) { return Variable(a, Z3_mk_bvnot(a, a), a.bitn); }


inline Variable ite(Variable const & a, Variable const & b, Variable const & c);


static inline Variable ashr(Variable const &a, Variable const  &b) {
	if(a.real()||b.real()){											
		return Variable(((ULong)a)>>((ULong)b), a);					
	}																
	else {															
		return Variable(a, Z3_mk_bvashr(a, a, b), a.bitn);
	}																
}																	
template<typename T>												
static inline Variable ashr(Variable &a, T b) {
	return ashr(a, Variable((ULong) b, a, a.bitn));
}																	
template<typename T>												
static inline Variable ashr(T a, Variable  &b) {
	return  ashr(Variable((ULong)a, b, b.bitn), b);
}																	

inline Variable::operator Z3_context() const { return m_ctx; }


#undef VariableOperator_unsigned 
#undef VariableOperator_signed_with_opname 
#undef VariableOperator_bool
#undef VariableOperator_signed 
#undef VariableOperatorDEF


#endif // !ASDREFGSER