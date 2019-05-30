#pragma once
#ifndef REGISTER_HL_CD
#define REGISTER_HL_CD
#define REGISTER_LEN 1000
template<int maxlength>
class Symbolic
{
	template <int maxlength>
	friend class Register;
public:
	/* SETFAST macro Setfast overstepping the bounds is not thread-safe(heap), so +32 solves the hidden bug !*/
	__declspec(align(32)) UChar m_fastindex[maxlength + 32];
	__declspec(align(8)) Z3_ast m_ast[maxlength];
	Z3_context m_ctx;
	inline Symbolic<maxlength>(Z3_context ctx) ;
	inline Symbolic<maxlength>(Z3_context ctx, Symbolic<maxlength> *father);
	inline ~Symbolic<maxlength>();
} ;


template<int maxlength>
class Record {
public:
	UChar m_flag[(maxlength >> 6) + 1];
	inline Record<maxlength>() ;
	
	template<int length>
	inline void write(int offset) ;

	class iterator
	{
	private:
		int _pcur;
		ULong *m_flag;
	public:
		inline iterator(UChar *flag);
		inline iterator(UChar *flag,int length) ;
		inline bool operator!=(const iterator &src);
		inline void operator++();
		inline int operator*();
		inline const int operator*()const;
	};

	inline iterator begin();
	inline iterator end();

};



template<int maxlength>
class Register {
public:
	Z3_context m_ctx;
	__declspec(align(32)) UChar m_bytes[maxlength];
	Symbolic<maxlength> *symbolic;
	Record<maxlength> *record;
	inline Register<maxlength>(Z3_context ctx, Bool _need_record);

	inline Register<maxlength>(Register<maxlength> &father_regs, Z3_context ctx, Bool _need_record) ;
	inline Register<maxlength>(const Register<maxlength> &father_regs) ;
	inline void operator = (Register<maxlength> &a) ;
	~Register<maxlength>() ;


	template<IRType ty>
	inline Vns Iex_Get(UInt);
	inline Vns Iex_Get(UInt, IRType);
	template<IRType ty>
	inline Vns Iex_Get(UInt, Z3_context);
	inline Vns Iex_Get(UInt, IRType, Z3_context);

	template<typename DataTy>
	inline void Ist_Put(UInt, DataTy);
	inline void Ist_Put(UInt offset, __m128i data);
	inline void Ist_Put(UInt offset, __m128  data);
	inline void Ist_Put(UInt offset, __m128d data);
	inline void Ist_Put(UInt offset, __m256i data);
	inline void Ist_Put(UInt offset, __m256  data);
	inline void Ist_Put(UInt offset, __m256d data);

	template<unsigned int bitn>
	inline void Ist_Put(UInt, Z3_ast);
	inline void Ist_Put(UInt, Vns const &);

	template<int LEN>
	inline void clear(UInt);

	inline void write_regs(int offset, void*, int length);
	inline void read_regs(int offset, void*, int length);
private:
	inline void Ist_Put(UInt, Z3_ast) = delete;
	inline void Ist_Put(UInt, Z3_ast&) = delete;
};


#endif //REGISTER_HL

