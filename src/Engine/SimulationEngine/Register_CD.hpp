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
	Symbolic<maxlength> *symbolic;
	__declspec(align(32)) UChar m_bytes[maxlength];
	Record<maxlength> *record;
	inline Register<maxlength>(Z3_context ctx, Bool _need_record);

	inline Register<maxlength>(Register<maxlength> &father_regs, Z3_context ctx, Bool _need_record) ;
	inline Register<maxlength>(const Register<maxlength> &father_regs) ;
	inline void operator = (Register<maxlength> &a) ;
	~Register<maxlength>() ;

	inline Variable Iex_Get_Translate(UInt, IRType,Z3_context toctx);
	inline Variable Iex_Get(UInt, IRType);

	template<memTAG Tag>
	inline void Ist_Put(UInt, Variable&);

	template<int LEN>
	inline void clear(UInt);

	inline void write_regs(int offset, void*, int length);
	inline void read_regs(int offset, void*, int length);
};








template<>
class Register<REGISTER_LEN> {
public:
	Z3_context m_ctx;
	Bool Need_Record;
	Z3_ast m_ast[REGISTER_LEN];
	/* SETFAST macro Setfast overstepping the bounds is not thread-safe(heap), so +32 solves the hidden bug !*/
	__declspec(align(32)) UChar m_fastindex[REGISTER_LEN + 32];
	__declspec(align(32)) UChar m_bytes[REGISTER_LEN];

	Record<REGISTER_LEN> record;
	inline Register(Z3_context ctx, Bool _need_record) ;
	inline Register(Register<REGISTER_LEN>& father_regs, Z3_context ctx, Bool _need_record) ;
	Register(const Register<REGISTER_LEN> &father_regs) ;
	inline void operator = (Register<REGISTER_LEN> &a) ;
	~Register() ;

	
	inline Variable Iex_Get(UInt offset, IRType ty);

	inline Variable Iex_Get_Translate(UInt offset, IRType ty, Z3_context toctx);
	
	template<memTAG Tag>
	inline void Ist_Put(UInt offset, Variable &ir);

	inline void Ist_Put(UInt offset, Variable &ir);

	template<Int LEN>
	inline void clear(UInt org_offset);

	inline void write_regs(int offset, void*, int length);
	inline void read_regs(int offset, void*, int length);
	inline void ShowRegs();
};








#endif //REGISTER_HL

