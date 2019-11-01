#pragma once


#include "../State_class.hpp"
#include "Z3_Target_Call.hpp"


static inline ULong resultsr(Vns& const retv) {
    Z3_inc_ref(retv, retv);
    register ULong ret = (ULong)(Z3_ast)retv;
    if (ret & (~((1ull << 48) - 1))) {
        vex_printf("system error");
    }
    return (ret & ((1ull << 48) - 1)) | (0xfa1dull << 48);;
}
#define TRRET(retv) (retv.real()? (ULong)(retv):resultsr(retv))


namespace helper {

	template<class _object, typename _PointerType = UChar, int offset = -1>
	class Pointer;
	class _VexGuestAMD64State;

	template<typename _PoinerType>
	static inline void operator_set(MEM &obj, Vns const &_where, _PoinerType data) {
		obj.Ist_Store(_where, data);
	}
	
	template<int maxlength,typename _PoinerType>
	static inline void operator_set(Register<maxlength> &obj, Vns const &_where, _PoinerType data) {
		assert(_where.real());
		obj.Ist_Put(_where, data);
	}

	static inline void operator_set(MEM &obj, Vns const &_where, Vns const &data) {
		obj.Ist_Store(_where, data);
	}

	template<int maxlength>
	static inline void operator_set(Register<maxlength> &obj, Vns const &_where, Vns const &data) {
		assert(_where.real());
		obj.Ist_Put(_where, data);
	}


	template<int bitn>
	static inline Vns operator_get(MEM &obj, Vns const &_where) {
		return obj.Iex_Load<((IRType)bitn)>(_where);
	}

	template<int bitn>
	static inline Vns operator_get(Register<1000> &obj, Vns const &_where) {
		assert(_where.real());
		return obj.Iex_Get<((IRType)bitn)>(_where);
	}


#define ISUNSIGNED_TYPE(type) ((type)-1 > 0)


	class C_Vns :public Vns {
	public:

		C_Vns(const Vns&_v) :Vns(_v) {};

		template<typename T>
		inline operator T() const {
			if (symbolic()) {
				std::cout << " error: I got a symbolic Vns. TriggerBug only support numrel there.\nyou can hook and pass this code with your operator" << std::endl;
			}
			assert(real());
			return *(T*)(&this->pack);
		}

	};




	template<class _object, typename _PointerType = UChar, int offset = -1, int shift = 0, int bits = (sizeof(_PointerType)<<3)>
	class inPointer {
		template<class __object, typename __PointerType = UChar, int _offset>
		friend class Pointer;
		friend class _VexGuestAMD64State;
	public:
		_object*m_obj;
		Vns		m_point;
		UShort	m_step;


		inline inPointer(_object &obj, ADDR _p) :
			m_obj(&obj),
			m_point((Z3_context)obj, _p),
			m_step(sizeof(_PointerType))
		{
		};

		inline inPointer(_object &obj, Vns const &_p) :
			m_obj(&obj),
			m_point(_p),
			m_step(sizeof(_PointerType))
		{
		};

		template<int maxlength>
		inline inPointer(Register<maxlength> &obj) :
			m_obj(&obj),
			m_point(obj.m_ctx, offset),
			m_step(sizeof(_PointerType))
		{
			assert(offset != -1);
		};

		inline inPointer(MEM &obj) :
			m_obj(&obj),
			m_point(obj.m_ctx, offset),
			m_step(sizeof(_PointerType))
		{
			assert(offset != -1);
		}


		template<typename _dataType>
		void operator=(_dataType data) {
			helper::operator_set(operator _object& (), m_point, (_PointerType)data);
		}

		void operator=(Vns const & data) {
			if ((sizeof(_PointerType) << 3) == data.bitn) {
				helper::operator_set(operator _object& (), m_point, data);
			}
			else if ((sizeof(_PointerType) << 3) > data.bitn) {
				if (ISUNSIGNED_TYPE(_PointerType)) {
					helper::operator_set<_PointerType>(operator _object& (), m_point, data.zext(data.bitn - (sizeof(_PointerType) << 3)));
				}
				else {
					helper::operator_set<_PointerType>(operator _object& (), m_point, data.sext(data.bitn - (sizeof(_PointerType) << 3)));
				}
			}
			else {
				helper::operator_set(operator _object& (), m_point, data.extract<(int)((sizeof(_PointerType) << 3) - 1), 0>());
			}
		}


		inline operator _object& () const {
			return const_cast<_object&>(*m_obj);
		}

		template<typename _dataType>
		operator _dataType() const {
			auto result = operator Vns();
			assert(result.real());
			return (_dataType)(_PointerType)result;
		}

		operator Vns() const {
            if (((sizeof(_PointerType) << 3) == bits)&&(shift==0)) {
                return operator_get<(sizeof(_PointerType) << 3)>(operator _object& (), this->m_point);
            }
            if (ISUNSIGNED_TYPE(_PointerType)) {
                return operator_get<(sizeof(_PointerType) << 3)>(operator _object& (), this->m_point).extract<(shift + bits - 1), shift>().zext((sizeof(_PointerType) << 3) - bits);
            }
            else {
                return operator_get<(sizeof(_PointerType) << 3)>(operator _object& (), this->m_point).extract<(shift + bits - 1), shift>().sext((sizeof(_PointerType) << 3) - bits);
            }
		}

		Pointer<_object, _PointerType> operator &() const {
			return Pointer<_object, _PointerType>(operator _object& (), m_point);
		}

		template<class __object, typename __PointerType>
		inline operator Pointer<__object, __PointerType>() const
		{
			return Pointer<__object, __PointerType>(operator _object& (), this->m_point);
		}

#define inPointer_operator(op)							\
		template<typename _dataType>					\
		C_Vns operator op(_dataType data) {				\
			return inPointer::operator Vns() op data;	\
		}



		template<typename _dataType>					
		C_Vns operator <=(_dataType data) {
			if (ISUNSIGNED_TYPE(_PointerType)) {
				return inPointer::operator Vns() <= data;
			}else{
				return le(inPointer::operator Vns(), data);					
			}											
		}
		template<typename _dataType>
		C_Vns operator <(_dataType data) {
			if (ISUNSIGNED_TYPE(_PointerType)) {
				return inPointer::operator Vns() < data;
			}
			else {
				return lt(inPointer::operator Vns(), data);
			}
		}
		template<typename _dataType>
		C_Vns operator >=(_dataType data) {
			if (ISUNSIGNED_TYPE(_PointerType)) {
				return inPointer::operator Vns() >= data;
			}
			else {
				return ge(inPointer::operator Vns(), data);
			}
		}
		template<typename _dataType>
		C_Vns operator >(_dataType data) {
			if (ISUNSIGNED_TYPE(_PointerType)) {
				return inPointer::operator Vns() > data;
			}
			else {
				return gt(inPointer::operator Vns(), data);
			}
		}
		inPointer_operator(+);
		inPointer_operator(-);
		inPointer_operator(*);
		inPointer_operator(/);
		inPointer_operator(>>);
		inPointer_operator(<<);
		inPointer_operator(|);
		inPointer_operator(&);
		inPointer_operator(==);


#undef inPointer_operator
	private:
		operator z3::expr()  = delete;
		operator z3::expr&()  = delete;
		operator const z3::expr() = delete;
		operator const z3::expr&() = delete;

	};



#define inPointer_operator2(op)			        \
template<class  T>                              \
C_Vns operator op(Vns const &a, T const& b) {   \
	return a op (Vns)b; \
}

    inPointer_operator2(+);
    inPointer_operator2(-);
    inPointer_operator2(*);
    inPointer_operator2(/ );
    inPointer_operator2(>> );
    inPointer_operator2(<< );
    inPointer_operator2(| );
    inPointer_operator2(&);
    inPointer_operator2(== );

#undef inPointer_operator2

	template<class _object, typename _PointerType = UChar, int offset = -1>
	class Pointer {
	public:
		_object*m_obj;
		Vns		m_point;
		UShort	m_step;

		inline Pointer(_object  &obj, Addr64 _p) :
			m_obj(&obj), 
			m_point((Z3_context)obj, _p),
			m_step(sizeof(_PointerType)) 
		{};
		inline Pointer(_object  &obj, Vns const &_p) :
			m_obj(&obj),
			m_point(_p), 
			m_step(sizeof(_PointerType)) 
		{};

		template<int maxlength>
		inline Pointer(Register<maxlength> &obj) :
			m_obj(&obj),
			m_point(obj.m_ctx, offset),
			m_step(sizeof(_PointerType)) 
		{
			assert(offset != -1);
		};

		template<class __object, typename __PointerType>
		inline Pointer(const Pointer<__object, __PointerType>& p) :
			m_obj(p.m_obj),
			m_point(p.m_point),
			m_step(sizeof(_PointerType))
		{
		};

		template<class __object, typename __PointerType>
		void operator=(Pointer<__object, __PointerType>& _where) {
			~Pointer();
			m_obj = _where.m_obj;
			m_point = _where.m_point;
		}


		template<typename _dataType>
		void operator=(_dataType _where) {
			assert(offset == -1);
			m_point = (void *)_where;
		}


		void operator=(Vns const & data) {
			assert(data.bitn == m_point.bitn);
			m_point = _where;
		}

		operator _object& () const {
			return const_cast<_object&>(*m_obj);
		}

		Pointer<_object, _PointerType> operator &() const = delete;

		operator Vns() const {
			return this->m_point;
		}

		template<typename _dataType>
		operator _dataType() const {
			return (_dataType)this->m_point;
		}

		helper::inPointer<_object, _PointerType> operator*() const {
			return helper::inPointer<_object, _PointerType>(*this, this->m_point);
		}


		template<typename _whereType>
		helper::inPointer<_object, _PointerType> operator[](_whereType offset) {
			auto ins = (offset * sizeof(_PointerType));
			return helper::inPointer<_object, _PointerType>(operator _object&(), m_point + ins);
		}

		~Pointer() {
			
		}

	};


	/* 
	int* p = 0x273823988;
	int a = *p; 
	int* p1 = &p[10];
	long long* p1 = (long long*)&p[10];
	long long d = * p1;
	long long d2 = * p1 + 10
	----------------
	helper::Int_ p(state.mem, 0x273823988);
	Int a = *p;
	helper::Long_ p1= (helper::Long_)&p[10];
	long long d = * p1;
	long long d2 =* p1 + 10;
	----------------
	Regs::AMD64 reg(s.regs);
	reg.guest_RAX = 0x45;
	reg.guest_FPREG[2] = 0x23336565;
	*/

	using Float_ = Pointer<MEM, Float>;
	using Double_ = Pointer<MEM, Double>;

	using Bool_ = Pointer<MEM, Bool>;
	using UChar_ = Pointer<MEM, UChar>;
	using SChar_ = Pointer<MEM, SChar>;
	using Char_ = Pointer<MEM, SChar>;
	using UShort_ = Pointer<MEM, UShort>;
	using Short_ = Pointer<MEM, SShort>;
	using SShort_ = Pointer<MEM, SShort>;
	using UInt_ = Pointer<MEM, UInt>;
	using Int_= Pointer<MEM, Int>;
	using SInt_ = Pointer<MEM, Int>;
	using ULong_ = Pointer<MEM, ULong>;
	using SLong_ = Pointer<MEM, SLong>;
	using Long_ = Pointer<MEM, SLong>;
	using m128_ = Pointer<MEM, __m128i>;
	using m256_ = Pointer<MEM, __m256i>;
	using V256_ = Pointer<MEM, V256>;
	using V128_ = Pointer<MEM, V128>;

	using _Float = inPointer<MEM, Float>;
	using _Double = inPointer<MEM, Double>;
	using _Bool = inPointer<MEM, Bool>;
	using _UChar = inPointer<MEM, UChar>;
	using _SChar = inPointer<MEM, SChar>;
	using _Char = inPointer<MEM, SChar>;
	using _UShort = inPointer<MEM, UShort>;
	using _Short = inPointer<MEM, SShort>;
	using _SShort = inPointer<MEM, SShort>;
	using _UInt = inPointer<MEM, UInt>;
	using _Int = inPointer<MEM, Int>;
	using _SInt = inPointer<MEM, Int>;
	using _ULong = inPointer<MEM, ULong>;
	using _SLong = inPointer<MEM, SLong>;
	using _m128 = inPointer<MEM, __m128i>;
	using _m256 = inPointer<MEM, __m256i>;
	using _V256 = inPointer<MEM, V256>;
	using _V128 = inPointer<MEM, V128>;


}

//register_names = { 
//16: 'rax', 24 : 'rcx', 32 : 'rdx', 40 : 'rbx', 48 : 'rsp', 56 : 'rbp', 64 : 'rsi', 72 : 'rdi', 
//80 : 'r8', 88 : 'r9', 96 : 'r10', 104 : 'r11', 112 : 'r12', 120 : 'r13', 128 : 'r14', 136 : 'r15', 
//144 : 'cc_op', 152 : 'cc_dep1', 160 : 'cc_dep2', 168 : 'cc_ndep', 176 : 'd', 184 : 'rip', 192 : 'ac', 200 : 'id', 208 : 'fs', 216 : 'sseround', 
//224 : 'ymm0', 256 : 'ymm1', 288 : 'ymm2', 320 : 'ymm3', 352 : 'ymm4', 384 : 'ymm5', 416 : 'ymm6', 448 : 'ymm7', 480 : 'ymm8', 512 : 'ymm9', 544 : 'ymm10', 576 : 'ymm11', 608 : 'ymm12', 640 : 'ymm13', 672 : 'ymm14', 704 : 'ymm15', 736 : 'ymm16', 
//768 : 'ftop', 776 : 'mm0',784 : "mm1",792 : "mm2",800 : "mm3",808 : "mm4",816 : "mm5",824 : "mm6",832 : "mm7", 840 : 'fptag', 848 : 'fpround', 856 : 'fc3210', 864 : 'emnote',872 : 'cmstart', 
//880 : 'cmlen', 888 : 'nraddr', 904 : 'gs', 912 : 'ip_at_syscall' }






template<typename Type = UChar, UInt offset = -1>
class Reg  {
    Register<REGISTER_LEN>& m_obj;
public:

    Reg(Register<REGISTER_LEN>& r) :
        m_obj(r)
    { }

    Reg(State& r) :
        m_obj(r.regs)
    { }



    Register<REGISTER_LEN>& obj() const{
        return static_cast<Register<REGISTER_LEN> &>(m_obj);
    }

    template<typename T>
    inline operator T () const {
        return (T)obj().Iex_Get<(IRType)(sizeof(Type)<<3)>(offset);
    }

    inline operator Vns () const{
        return obj().Iex_Get<(IRType)(sizeof(Type) << 3)>(offset);
    }

    template<typename T>
    inline void operator=(T  data) {
        obj().Ist_Put(offset, data);
    }
    
#define REG_OPERATOR(op)					\
		template<typename _dataType>		\
		Vns operator op(_dataType data) const{\
			return operator Vns() op data;	\
		}

    REG_OPERATOR(+);
    REG_OPERATOR(-);
    REG_OPERATOR(*);
    REG_OPERATOR(/ );
    REG_OPERATOR(>> );
    REG_OPERATOR(<< );
    REG_OPERATOR(| );
    REG_OPERATOR(&);
    REG_OPERATOR(== );

#undef REG_OPERATOR

private:
    template<typename T>
    T operator &() = delete;
    template<typename T>
    T operator &() const = delete;

    operator z3::expr() = delete;
    operator z3::expr& () = delete;
    operator z3::expr& () const = delete;
    operator const z3::expr() = delete;
    operator const z3::expr& () = delete;
    operator const z3::expr& () const = delete;

};

template<typename Type = UChar, UInt offset = -1>
class RegL {
    Register<REGISTER_LEN>& obj;
public:

    RegL(Register<REGISTER_LEN>& r) :
        obj(r)
    { }

    RegL(State& r) :
        obj(r.regs)
    { }

};

template<typename Type = UChar>
class GM {
    Vns m_base;
    MEM& m_obj;
public:
    GM(MEM& obj, Vns& const base):
        m_obj(obj),
        m_base(base)
    {}

    GM(MEM& obj, ADDR base):
        m_obj(obj),
        m_base(obj, base)
    {}

    template<typename T>
    GM(MEM& obj, T base) :
        m_obj(obj),
        m_base(obj, (ADDR)base)
    {}

    MEM& obj() const {
        return static_cast<MEM const&>(m_obj);
    }

    template<typename T>
    inline operator T () const {
        return (T)obj().Iex_Load<(IRType)(sizeof(Type) << 3)>(m_base);
    }

    inline operator Vns () const {
        return obj().Iex_Load<(IRType)(sizeof(Type) << 3)>(m_base);
    }

    template<typename T>
    inline void operator=(T const data) {
        obj().Ist_Store(m_base, data);
    }

    void operator=(Vns const& data) {
        if ((sizeof(Type) << 3) == data.bitn) {
            obj().Ist_Store(m_base, data);
        }
        else if ((sizeof(Type) << 3) > data.bitn) {
            if (ISUNSIGNED_TYPE(Type)) {
                obj().Ist_Store(m_base, data.zext(data.bitn - (sizeof(Type) << 3)));
            }
            else {
               obj().Ist_Store( m_base, data.sext(data.bitn - (sizeof(Type) << 3)));
            }
        }
        else {
            obj().Ist_Store(m_base, data.extract<(int)((sizeof(Type) << 3) - 1), 0>());
        }
    }

    inline GM<Type> operator [](UInt idx) {
        return GM<Type>(obj(), m_base + idx * (sizeof(Type)));
    }



#define REG_OPERATOR(op)					\
		template<typename _dataType>		\
		Vns operator op(_dataType data) const{\
			return operator Vns() op data;	\
		}

    REG_OPERATOR(+);
    REG_OPERATOR(-);
    REG_OPERATOR(*);
    REG_OPERATOR(/ );
    REG_OPERATOR(>> );
    REG_OPERATOR(<< );
    REG_OPERATOR(| );
    REG_OPERATOR(&);
    REG_OPERATOR(== );

#undef REG_OPERATOR

private:
    template<typename T>
    T operator &() = delete;
    template<typename T>
    T operator &() const = delete;

    operator z3::expr() = delete;
    operator z3::expr& () = delete;
    operator z3::expr& () const = delete;
    operator const z3::expr() = delete;
    operator const z3::expr& () = delete;
    operator const z3::expr& () const = delete;
};

class _VexGuestAMD64State {
public:
    Reg<ULong, 0>     host_EvC_FAILADDR;
    Reg<UInt, 8>      host_EvC_COUNTER;
    Reg<UInt, 12>     pad0;
    Reg<ULong, 16>    guest_RAX;
    Reg<ULong, 24>    guest_RCX;
    Reg<ULong, 32>    guest_RDX;
    Reg<ULong, 40>    guest_RBX;
    Reg<ULong, 48>    guest_RSP;
    Reg<ULong, 56>    guest_RBP;
    Reg<ULong, 64>    guest_RSI;
    Reg<ULong, 72>    guest_RDI;
    Reg<ULong, 80>    guest_R8;
    Reg<ULong, 88>    guest_R9;
    Reg<ULong, 96>    guest_R10;
    Reg<ULong, 104>   guest_R11;
    Reg<ULong, 112>   guest_R12;
    Reg<ULong, 120>   guest_R13;
    Reg<ULong, 128>   guest_R14;
    Reg<ULong, 136>   guest_R15;
    Reg<ULong, 144>   guest_CC_OP;
    Reg<ULong, 152>   guest_CC_DEP1;
    Reg<ULong, 160>   guest_CC_DEP2;
    Reg<ULong, 168>   guest_CC_NDEP;
    Reg<ULong, 176>   guest_DFLAG;
    Reg<ULong, 184>   guest_RIP;
    Reg<ULong, 192>   guest_ACFLAG;
    Reg<ULong, 200>   guest_IDFLAG;
    Reg<ULong, 208>   guest_FS_CONST;
    Reg<ULong, 216>   guest_SSEROUND;
    Reg<__m256i, 224> guest_YMM0;
    Reg<__m256i, 256> guest_YMM1;
    Reg<__m256i, 288> guest_YMM2;
    Reg<__m256i, 320> guest_YMM3;
    Reg<__m256i, 352> guest_YMM4;
    Reg<__m256i, 384> guest_YMM5;
    Reg<__m256i, 416> guest_YMM6;
    Reg<__m256i, 448> guest_YMM7;
    Reg<__m256i, 480> guest_YMM8;
    Reg<__m256i, 512> guest_YMM9;
    Reg<__m256i, 544> guest_YMM10;
    Reg<__m256i, 576> guest_YMM11;
    Reg<__m256i, 608> guest_YMM12;
    Reg<__m256i, 640> guest_YMM13;
    Reg<__m256i, 672> guest_YMM14;
    Reg<__m256i, 704> guest_YMM15;
    Reg<__m256i, 736> guest_YMM16;
    Reg<UInt, 768>    guest_FTOP;
    Reg<UInt, 772>    pad1;
    RegL<ULong, 776>  guest_FPREG;
    RegL<UChar, 840>  guest_FPTAG;
    Reg<ULong, 848>   guest_FPROUND;
    Reg<ULong, 856>   guest_FC3210;
    Reg<UInt, 864>    guest_EMNOTE;
    Reg<UInt, 868>    pad2;
    Reg<ULong, 872>   guest_CMSTART;
    Reg<ULong, 880>   guest_CMLEN;
    Reg<ULong, 888>   guest_NRADDR;
    Reg<ULong, 896>   guest_SC_CLASS;
    Reg<ULong, 904>   guest_GS_CONST;
    Reg<ULong, 912>   guest_IP_AT_SYSCALL;
    State& m_state;
public:
	_VexGuestAMD64State(State &s):
        m_state(s),
        host_EvC_FAILADDR(s),
        host_EvC_COUNTER(s),
        pad0(s),
        guest_RAX(s),
        guest_RCX(s),
        guest_RDX(s),
        guest_RBX(s),
        guest_RSP(s),
        guest_RBP(s),
        guest_RSI(s),
        guest_RDI(s),
        guest_R8(s),
        guest_R9(s),
        guest_R10(s),
        guest_R11(s),
        guest_R12(s),
        guest_R13(s),
        guest_R14(s),
        guest_R15(s),
        guest_CC_OP(s),
        guest_CC_DEP1(s),
        guest_CC_DEP2(s),
        guest_CC_NDEP(s),
        guest_DFLAG(s),
        guest_RIP(s),
        guest_ACFLAG(s),
        guest_IDFLAG(s),
        guest_FS_CONST(s),
        guest_SSEROUND(s),
        guest_YMM0(s),
        guest_YMM1(s),
        guest_YMM2(s),
        guest_YMM3(s),
        guest_YMM4(s),
        guest_YMM5(s),
        guest_YMM6(s),
        guest_YMM7(s),
        guest_YMM8(s),
        guest_YMM9(s),
        guest_YMM10(s),
        guest_YMM11(s),
        guest_YMM12(s),
        guest_YMM13(s),
        guest_YMM14(s),
        guest_YMM15(s),
        guest_YMM16(s),
        guest_FTOP(s),
        pad1(s),
        guest_FPREG(s),
        guest_FPTAG(s),
        guest_FPROUND(s),
        guest_FC3210(s),
        guest_EMNOTE(s),
        pad2(s),
        guest_CMSTART(s),
        guest_CMLEN(s),
        guest_NRADDR(s),
        guest_SC_CLASS(s),
        guest_GS_CONST(s),
        guest_IP_AT_SYSCALL(s)
	{

	}

    inline operator Z3_context() {
        return m_state.m_ctx;
    }

    inline operator Register<REGISTER_LEN> &() {
        return m_state.regs;
    }

    inline operator MEM&() {
        return m_state.mem;
    }
};


class _VexGuestX86State {
public:

    Reg<UInt, 0>        host_EvC_FAILADDR;
    Reg<UInt, 4>        host_EvC_COUNTER;
    Reg<UInt, 8>        guest_EAX;
    Reg<UInt, 12>       guest_ECX;
    Reg<UInt, 16>       guest_EDX;
    Reg<UInt, 20>       guest_EBX;
    Reg<UInt, 24>       guest_ESP;
    Reg<UInt, 28>       guest_EBP;
    Reg<UInt, 32>       guest_ESI;
    Reg<UInt, 36>       guest_EDI;
    Reg<UInt, 40>       guest_CC_OP;
    Reg<UInt, 44>       guest_CC_DEP1;
    Reg<UInt, 48>       guest_CC_DEP2;
    Reg<UInt, 52>       guest_CC_NDEP;
    Reg<UInt, 56>       guest_DFLAG;
    Reg<UInt, 60>       guest_IDFLAG;
    Reg<UInt, 64>       guest_ACFLAG;
    Reg<UInt, 68>       guest_EIP;
    RegL<ULong, 72>     guest_FPREG;
    RegL<UChar, 136>    guest_FPTAG;
    Reg<UInt, 144>      guest_FPROUND;
    Reg<UInt, 148>      guest_FC3210;
    Reg<UInt, 152>      guest_FTOP;
    Reg<UInt, 156>      guest_SSEROUND;
    Reg<U128, 160>      guest_XMM0;
    Reg<U128, 176>      guest_XMM1;
    Reg<U128, 192>      guest_XMM2;
    Reg<U128, 208>      guest_XMM3;
    Reg<U128, 224>      guest_XMM4;
    Reg<U128, 240>      guest_XMM5;
    Reg<U128, 256>      guest_XMM6;
    Reg<U128, 272>      guest_XMM7;
    Reg<UShort, 288>    guest_CS;
    Reg<UShort, 290>    guest_DS;
    Reg<UShort, 292>    guest_ES;
    Reg<UShort, 294>    guest_FS;
    Reg<UShort, 296>    guest_GS;
    Reg<UShort, 298>    guest_SS;
    Reg<ULong, 304>     guest_LDT;
    Reg<ULong, 312>     guest_GDT;
    Reg<UInt, 320>      guest_EMNOTE;
    Reg<UInt, 324>      guest_CMSTART;
    Reg<UInt, 328>      guest_CMLEN;
    Reg<UInt, 332>      guest_NRADDR;
    Reg<UInt, 336>      guest_SC_CLASS;
    Reg<UInt, 340>      guest_IP_AT_SYSCALL;
    Reg<UInt, 344>      padding1;
    Reg<UInt, 348>      padding2;
    Reg<UInt, 352>      padding3;
public:
    _VexGuestX86State(State& s):
        host_EvC_FAILADDR(s),
        host_EvC_COUNTER(s),
        guest_EAX(s),
        guest_ECX(s),
        guest_EDX(s),
        guest_EBX(s),
        guest_ESP(s),
        guest_EBP(s),
        guest_ESI(s),
        guest_EDI(s),
        guest_CC_OP(s),
        guest_CC_DEP1(s),
        guest_CC_DEP2(s),
        guest_CC_NDEP(s),
        guest_DFLAG(s),
        guest_IDFLAG(s),
        guest_ACFLAG(s),
        guest_EIP(s),
        guest_FPREG(s),
        guest_FPTAG(s),
        guest_FPROUND(s),
        guest_FC3210(s),
        guest_FTOP(s),
        guest_SSEROUND(s),
        guest_XMM0(s),
        guest_XMM1(s),
        guest_XMM2(s),
        guest_XMM3(s),
        guest_XMM4(s),
        guest_XMM5(s),
        guest_XMM6(s),
        guest_XMM7(s),
        guest_CS(s),
        guest_DS(s),
        guest_ES(s),
        guest_FS(s),
        guest_GS(s),
        guest_SS(s),
        guest_LDT(s),
        guest_GDT(s),
        guest_EMNOTE(s),
        guest_CMSTART(s),
        guest_CMLEN(s),
        guest_NRADDR(s),
        guest_SC_CLASS(s),
        guest_IP_AT_SYSCALL(s),
        padding1(s),
        padding2(s),
        padding3(s)
    {

    }

};

namespace _X86SegDescr {
    using LimitLow = helper::inPointer<MEM, UShort, 0>;
    using BaseLow = helper::inPointer<MEM, UShort, 2>;
    using BaseMid = helper::inPointer<MEM, UInt, 4, 0, 8>;
    using Type = helper::inPointer<MEM, UInt, 4, 8, 5>;
    using Dpl = helper::inPointer<MEM, UInt, 4, 13, 2>;
    using Pres = helper::inPointer<MEM, UInt, 4, 15, 1>;
    using LimitHi = helper::inPointer<MEM, UInt, 4, 16, 4>;
    using Sys = helper::inPointer<MEM, UInt, 4, 20, 1>;
    using Reserved_0 = helper::inPointer<MEM, UInt, 4, 21, 1>;
    using Default_Big = helper::inPointer<MEM, UInt, 4, 22, 1>;
    using Granularity = helper::inPointer<MEM, UInt, 4, 23, 1>;
    using BaseHi = helper::inPointer<MEM, UInt, 4, 24, 8>;
    using word1 = helper::inPointer<MEM, UInt, 0>;
    using word2 = helper::inPointer<MEM, UInt, 4>;
}

//class _VexGuestX86SegDescr : public Guest_State {
//public:
//    class _Bits {
//    public:
//        _X86SegDescr::LimitLow LimitLow;
//        _X86SegDescr::BaseLow BaseLow;
//        _X86SegDescr::BaseMid BaseMid;
//        _X86SegDescr::Type Type;
//        _X86SegDescr::Dpl Dpl;
//        _X86SegDescr::Pres Pres;
//        _X86SegDescr::LimitHi LimitHi;
//        _X86SegDescr::Sys Sys;
//        _X86SegDescr::Reserved_0 Reserved_0;
//        _X86SegDescr::Default_Big Default_Big;
//        _X86SegDescr::Granularity Granularity;
//        _X86SegDescr::BaseHi BaseHi;
//        _Bits(State &state, ADDR base):
//            LimitLow(state.mem, base + 0),
//            BaseLow(state.mem, base + 2),
//            BaseMid(state.mem, base + 4),
//            Type(state.mem, base + 4),
//            Dpl(state.mem, base + 4),
//            Pres(state.mem, base + 4),
//            LimitHi(state.mem, base + 4),
//            Sys(state.mem, base + 4),
//            Reserved_0(state.mem, base + 4),
//            Default_Big(state.mem, base + 4),
//            Granularity(state.mem, base + 4),
//            BaseHi(state.mem, base + 4)
//        {
//        }
//    };
//    class _Words {
//    public:
//        _X86SegDescr::word1 word1;
//        _X86SegDescr::word2 word2;
//        _Words(State& state, ADDR base) :
//            word1(state.mem, base),
//            word2(state.mem, base + 4)
//        {
//        }
//    };
//
//    class _LdtEnt {
//    public:
//        _Words Words;
//        _Bits Bits;
//        _LdtEnt(State &state, ADDR base) :
//            Words(state, base),
//            Bits(state, base)
//        {
//        }
//    };
//
//    _LdtEnt LdtEnt;
//    _VexGuestX86SegDescr(State &state, void* base) :
//        Guest_State(state), 
//        LdtEnt(state, (ADDR)base)
//    {
//    }
//};

namespace Regs {
	using AMD64 = _VexGuestAMD64State;
    using X86 = _VexGuestX86State;
    //using X86SegDescr = _VexGuestX86SegDescr;
}

#undef ISUNSIGNED_TYPE