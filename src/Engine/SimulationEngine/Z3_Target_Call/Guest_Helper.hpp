#pragma once


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

namespace _AMD64State {
	using host_EvC_FAILADDR = helper::inPointer<Register<1000>, ULong, 0>;
	using host_EvC_COUNTER	= helper::inPointer<Register<1000>, UInt, 8>;
	using pad0				= helper::inPointer<Register<1000>, UInt, 12>;
	using guest_RAX			= helper::inPointer<Register<1000>, ULong, 16>;
	using guest_RCX			= helper::inPointer<Register<1000>, ULong, 24>;
	using guest_RDX			= helper::inPointer<Register<1000>, ULong, 32>;
	using guest_RBX			= helper::inPointer<Register<1000>, ULong, 40>;
	using guest_RSP			= helper::inPointer<Register<1000>, ULong, 48>;
	using guest_RBP			= helper::inPointer<Register<1000>, ULong, 56>;
	using guest_RSI			= helper::inPointer<Register<1000>, ULong, 64>;
	using guest_RDI			= helper::inPointer<Register<1000>, ULong, 72>;
	using guest_R8			= helper::inPointer<Register<1000>, ULong, 80>;
	using guest_R9			= helper::inPointer<Register<1000>, ULong, 88>;
	using guest_R10			= helper::inPointer<Register<1000>, ULong, 96>;
	using guest_R11			= helper::inPointer<Register<1000>, ULong, 104>;
	using guest_R12			= helper::inPointer<Register<1000>, ULong, 112>;
	using guest_R13			= helper::inPointer<Register<1000>, ULong, 120>;
	using guest_R14			= helper::inPointer<Register<1000>, ULong, 128>;
	using guest_R15			= helper::inPointer<Register<1000>, ULong, 136>;
	
	using guest_CC_OP		= helper::inPointer<Register<1000>, ULong, 144>;
	using guest_CC_DEP1		= helper::inPointer<Register<1000>, ULong, 152>;
	using guest_CC_DEP2		= helper::inPointer<Register<1000>, ULong, 160>;
	using guest_CC_NDEP		= helper::inPointer<Register<1000>, ULong, 168>;

	using guest_DFLAG		= helper::inPointer<Register<1000>, ULong, 176>;
	using guest_RIP			= helper::inPointer<Register<1000>, ULong, 184>;
	using guest_ACFLAG		= helper::inPointer<Register<1000>, ULong, 192>;
	using guest_IDFLAG		= helper::inPointer<Register<1000>, ULong, 200>;
	using guest_FS_CONST	= helper::inPointer<Register<1000>, ULong, 208>;
	using guest_SSEROUND	= helper::inPointer<Register<1000>, ULong, 216>;

	using guest_YMM0		= helper::inPointer<Register<1000>, __m256i, 224>;
	using guest_YMM1		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 1>;
	using guest_YMM2		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 2>;
	using guest_YMM3		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 3>;
	using guest_YMM4		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 4>;
	using guest_YMM5		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 5>;
	using guest_YMM6		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 6>;
	using guest_YMM7		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 7>;
	using guest_YMM8		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 8>;
	using guest_YMM9		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 9>;
	using guest_YMM10		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 10>;
	using guest_YMM11		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 11>;
	using guest_YMM12		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 12>;
	using guest_YMM13		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 13>;
	using guest_YMM14		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 14>;
	using guest_YMM15		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 15>;
	using guest_YMM16		= helper::inPointer<Register<1000>, __m256i, 224 + 32 * 16>;

	using guest_FTOP		= helper::inPointer<Register<1000>, UInt, 768>;
	using pad1				= helper::inPointer<Register<1000>, UInt, 772>;
	using guest_FPREG		= helper::Pointer<Register<1000>, ULong, 776>;
	using guest_FPTAG		= helper::Pointer<Register<1000>, UChar, 840>;
	using guest_FPROUND		= helper::inPointer<Register<1000>, ULong, 848>;
	using guest_FC3210		= helper::inPointer<Register<1000>, ULong, 856>;

	using guest_EMNOTE		= helper::inPointer<Register<1000>, UInt, 864>;
	using pad2				= helper::inPointer<Register<1000>, UInt, 868>;
	using guest_CMSTART		= helper::inPointer<Register<1000>, ULong, 872>;
	using guest_CMLEN		= helper::inPointer<Register<1000>, ULong, 880>;
	using guest_NRADDR		= helper::inPointer<Register<1000>, ULong, 888>;
	using guest_SC_CLASS	= helper::inPointer<Register<1000>, ULong, 896>;
	using guest_GS_CONST	= helper::inPointer<Register<1000>, ULong, 904>;
	using guest_IP_AT_SYSCALL = helper::inPointer<Register<1000>, ULong, 912>;
}

namespace _X86State {
    using host_EvC_FAILADDR = helper::inPointer<Register<1000>, UInt, 0>;
    using host_EvC_COUNTER = helper::inPointer<Register<1000>, UInt, 4>;
    using guest_EAX = helper::inPointer<Register<1000>, UInt, 8>;
    using guest_ECX = helper::inPointer<Register<1000>, UInt, 12>;
    using guest_EDX = helper::inPointer<Register<1000>, UInt, 16>;
    using guest_EBX = helper::inPointer<Register<1000>, UInt, 20>;
    using guest_ESP = helper::inPointer<Register<1000>, UInt, 24>;
    using guest_EBP = helper::inPointer<Register<1000>, UInt, 28>;
    using guest_ESI = helper::inPointer<Register<1000>, UInt, 32>;
    using guest_EDI = helper::inPointer<Register<1000>, UInt, 36>;

    using guest_CC_OP = helper::inPointer<Register<1000>, UInt, 40>;
    using guest_CC_DEP1 = helper::inPointer<Register<1000>, UInt, 44>;
    using guest_CC_DEP2 = helper::inPointer<Register<1000>, UInt, 48>;
    using guest_CC_NDEP = helper::inPointer<Register<1000>, UInt, 52>;
    using guest_DFLAG = helper::inPointer<Register<1000>, UInt, 56>;
    using guest_IDFLAG = helper::inPointer<Register<1000>, UInt, 60>;
    using guest_ACFLAG = helper::inPointer<Register<1000>, UInt, 64>;

    using guest_EIP = helper::inPointer<Register<1000>, UInt, 68>;

    using guest_FPREG = helper::Pointer<Register<1000>, ULong, 72>;
    using guest_FPTAG = helper::Pointer<Register<1000>, UChar, 136>;
    using guest_FPROUND = helper::inPointer<Register<1000>, UInt, 144>; 
    using guest_FC3210 = helper::inPointer<Register<1000>, UInt, 148>;  
    using guest_FTOP = helper::inPointer<Register<1000>, UInt, 152>;    

    using guest_SSEROUND = helper::inPointer<Register<1000>, UInt, 156>;   
    using guest_XMM0 = helper::inPointer<Register<1000>, U128, 160>;       
    using guest_XMM1 = helper::inPointer<Register<1000>, U128, 160 + 1*16>;
    using guest_XMM2 = helper::inPointer<Register<1000>, U128, 160 + 2*16>;
    using guest_XMM3 = helper::inPointer<Register<1000>, U128, 160 + 3*16>;
    using guest_XMM4 = helper::inPointer<Register<1000>, U128, 160 + 4*16>;
    using guest_XMM5 = helper::inPointer<Register<1000>, U128, 160 + 5*16>;
    using guest_XMM6 = helper::inPointer<Register<1000>, U128, 160 + 6*16>;
    using guest_XMM7 = helper::inPointer<Register<1000>, U128, 160 + 7*16>;

    using guest_CS = helper::inPointer<Register<1000>, UShort, 288>;
    using guest_DS = helper::inPointer<Register<1000>, UShort, 290>;
    using guest_ES = helper::inPointer<Register<1000>, UShort, 292>;
    using guest_FS = helper::inPointer<Register<1000>, UShort, 294>;
    using guest_GS = helper::inPointer<Register<1000>, UShort, 296>;
    using guest_SS = helper::inPointer<Register<1000>, UShort, 298>;
    using guest_LDT = helper::inPointer<Register<1000>, ULong, 304>;
    using guest_GDT = helper::inPointer<Register<1000>, ULong, 312>;

    using guest_EMNOTE = helper::inPointer<Register<1000>, UInt, 320>;

    using guest_CMSTART = helper::inPointer<Register<1000>, UInt, 324>;
    using guest_CMLEN = helper::inPointer<Register<1000>, UInt, 328>;

    using guest_NRADDR = helper::inPointer<Register<1000>, UInt, 332>;

    using guest_SC_CLASS = helper::inPointer<Register<1000>, UInt, 336>;

    using guest_IP_AT_SYSCALL = helper::inPointer<Register<1000>, UInt, 340>;

    using padding1 = helper::inPointer<Register<1000>, UInt, 344>;
    using padding2 = helper::inPointer<Register<1000>, UInt, 348>;
    using padding3 = helper::inPointer<Register<1000>, UInt, 352>;
}



class Guest_State {
	State *state;
public:
	Guest_State(State &state):
		state(&state)
	{

	}
	operator MEM &() {
		return state->mem;
	}
	template<int len>
	operator Register<len> &() {
		return state->regs;
	}
};


class _VexGuestAMD64State:public Guest_State {
public:
	/* Event check fail addr, counter, and padding to make RAX 16
	 aligned. */
	/*   0 */ _AMD64State::host_EvC_FAILADDR host_EvC_FAILADDR;
	/*   8 */ _AMD64State::host_EvC_COUNTER host_EvC_COUNTER;
	/*  12 */ _AMD64State::pad0 pad0;
	/*  16 */ _AMD64State::guest_RAX guest_RAX;
	/*  24 */ _AMD64State::guest_RCX guest_RCX;
	/*  32 */ _AMD64State::guest_RDX guest_RDX;
	/*  40 */ _AMD64State::guest_RBX guest_RBX;
	/*  48 */ _AMD64State::guest_RSP guest_RSP;
	/*  56 */ _AMD64State::guest_RBP guest_RBP;
	/*  64 */ _AMD64State::guest_RSI guest_RSI;
	/*  72 */ _AMD64State::guest_RDI guest_RDI;
	/*  80 */ _AMD64State::guest_R8 guest_R8;
	/*  88 */ _AMD64State::guest_R9 guest_R9;
	/*  96 */ _AMD64State::guest_R10 guest_R10;
	/* 104 */ _AMD64State::guest_R11 guest_R11;
	/* 112 */ _AMD64State::guest_R12 guest_R12;
	/* 120 */ _AMD64State::guest_R13 guest_R13;
	/* 128 */ _AMD64State::guest_R14 guest_R14;
	/* 136 */ _AMD64State::guest_R15 guest_R15;
	/* 4-word thunk used to calculate O S Z A C P flags. */
	/* 144 */ _AMD64State::guest_CC_OP guest_CC_OP;
	/* 152 */ _AMD64State::guest_CC_DEP1 guest_CC_DEP1;
	/* 160 */ _AMD64State::guest_CC_DEP2 guest_CC_DEP2;
	/* 168 */ _AMD64State::guest_CC_NDEP guest_CC_NDEP;
	/* The D flag is stored here, encoded as either -1 or +1 */
	/* 176 */ _AMD64State::guest_DFLAG guest_DFLAG;
	/* 184 */ _AMD64State::guest_RIP guest_RIP;
	/* Bit 18 (AC) of eflags stored here, as either 0 or 1. */
	/* ... */ _AMD64State::guest_ACFLAG guest_ACFLAG;
	/* Bit 21 (ID) of eflags stored here, as either 0 or 1. */
	/* 192 */ _AMD64State::guest_IDFLAG guest_IDFLAG;
	/* Probably a lot more stuff too.
	   D,ID flags
	   16  128-bit SSE registers
	   all the old x87 FPU gunk
	   segment registers */

	   /* HACK to e.g. make tls on amd64-linux/solaris work.  %fs only ever seems
		  to hold a constant value (zero on linux main thread, 0x63 in other
		  threads), and so guest_FS_CONST holds
		  the 64-bit offset associated with this constant %fs value. */
	/* 200 */ _AMD64State::guest_FS_CONST guest_FS_CONST;

	/* YMM registers.  Note that these must be allocated
	   consecutively in order that the SSE4.2 PCMP{E,I}STR{I,M}
	   helpers can treat them as an array.  YMM16 is a fake reg used
	   as an intermediary in handling aforementioned insns. */
	/* 208 */_AMD64State::guest_SSEROUND guest_SSEROUND;
	/* 216 */_AMD64State::guest_YMM0 guest_YMM0;
	_AMD64State::guest_YMM1	guest_YMM1;
	_AMD64State::guest_YMM2	guest_YMM2;
	_AMD64State::guest_YMM3	guest_YMM3;
	_AMD64State::guest_YMM4	guest_YMM4;
	_AMD64State::guest_YMM5	guest_YMM5;
	_AMD64State::guest_YMM6	guest_YMM6;
	_AMD64State::guest_YMM7	guest_YMM7;
	_AMD64State::guest_YMM8	guest_YMM8;
	_AMD64State::guest_YMM9	guest_YMM9;
	_AMD64State::guest_YMM10 guest_YMM10;
	_AMD64State::guest_YMM11 guest_YMM11;
	_AMD64State::guest_YMM12 guest_YMM12;
	_AMD64State::guest_YMM13 guest_YMM13;
	_AMD64State::guest_YMM14 guest_YMM14;
	_AMD64State::guest_YMM15 guest_YMM15;
	_AMD64State::guest_YMM16 guest_YMM16;

	/* FPU */
	/* Note.  Setting guest_FTOP to be ULong messes up the
	   delicately-balanced PutI/GetI optimisation machinery.
	   Therefore best to leave it as a UInt. */
	_AMD64State::guest_FTOP guest_FTOP;
	_AMD64State::pad1 pad1;
	_AMD64State::guest_FPREG guest_FPREG;
	_AMD64State::guest_FPTAG guest_FPTAG;
	_AMD64State::guest_FPROUND guest_FPROUND;
	_AMD64State::guest_FC3210 guest_FC3210;

	/* Emulation notes */
	_AMD64State::guest_EMNOTE guest_EMNOTE;
	_AMD64State::pad2 pad2;

	/* Translation-invalidation area description.  Not used on amd64
	   (there is no invalidate-icache insn), but needed so as to
	   allow users of the library to uniformly assume that the guest
	   state contains these two fields -- otherwise there is
	   compilation breakage.  On amd64, these two fields are set to
	   zero by LibVEX_GuestAMD64_initialise and then should be
	   ignored forever thereafter. */
	_AMD64State::guest_CMSTART guest_CMSTART;
	_AMD64State::guest_CMLEN guest_CMLEN;

	/* Used to record the unredirected guest address at the start of
	   a translation whose start has been redirected.  By reading
	   this pseudo-register shortly afterwards, the translation can
	   find out what the corresponding no-redirection address was.
	   Note, this is only set for wrap-style redirects, not for
	   replace-style ones. */
	_AMD64State::guest_NRADDR guest_NRADDR;

	/* Used for Darwin syscall dispatching. */
	_AMD64State::guest_SC_CLASS guest_SC_CLASS;

	/* HACK to make e.g. tls on darwin work, wine on linux work, ...
	   %gs only ever seems to hold a constant value (e.g. 0x60 on darwin,
	   0x6b on linux), and so guest_GS_CONST holds the 64-bit offset
	   associated with this constant %gs value.  (A direct analogue
	   of the %fs-const hack for amd64-linux/solaris). */
	_AMD64State::guest_GS_CONST guest_GS_CONST;

	/* Needed for Darwin (but mandated for all guest architectures):
	   RIP at the last syscall insn (int 0x80/81/82, sysenter,
	   syscall).  Used when backing up to restart a syscall that has
	   been interrupted by a signal. */
	_AMD64State::guest_IP_AT_SYSCALL guest_IP_AT_SYSCALL;

public:
	_VexGuestAMD64State(State &state):
		Guest_State(state),
		host_EvC_FAILADDR(state.regs),
		host_EvC_COUNTER(state.regs),
		pad0(state.regs),
		pad1(state.regs),
		pad2(state.regs),
		guest_RAX(state.regs),
		guest_RCX(state.regs),
		guest_RDX(state.regs),
		guest_RBX(state.regs),
		guest_RSP(state.regs),
		guest_RBP(state.regs),
		guest_RSI(state.regs),
		guest_RDI(state.regs),
		guest_R8(state.regs),
		guest_R9(state.regs),
		guest_R10(state.regs),
		guest_R11(state.regs),
		guest_R12(state.regs),
		guest_R13(state.regs),
		guest_R14(state.regs),
		guest_R15(state.regs),
		guest_CC_OP(state.regs),
		guest_CC_DEP1(state.regs),
		guest_CC_DEP2(state.regs),
		guest_CC_NDEP(state.regs),
		guest_DFLAG(state.regs),
		guest_RIP(state.regs),
		guest_ACFLAG(state.regs),
		guest_IDFLAG(state.regs),
		guest_FS_CONST(state.regs),
		guest_SSEROUND(state.regs),
		guest_YMM0(state.regs),
		guest_YMM1(state.regs),
		guest_YMM2(state.regs),
		guest_YMM3(state.regs),
		guest_YMM4(state.regs),
		guest_YMM5(state.regs),
		guest_YMM6(state.regs),
		guest_YMM7(state.regs),
		guest_YMM8(state.regs),
		guest_YMM9(state.regs),
		guest_YMM10(state.regs),
		guest_YMM11(state.regs),
		guest_YMM12(state.regs),
		guest_YMM13(state.regs),
		guest_YMM14(state.regs),
		guest_YMM15(state.regs),
		guest_YMM16(state.regs),
		guest_FTOP(state.regs),
		guest_FPREG(state.regs),
		guest_FPTAG(state.regs),
		guest_FPROUND(state.regs),
		guest_FC3210(state.regs),
		guest_EMNOTE(state.regs),
		guest_CMSTART(state.regs),
		guest_CMLEN(state.regs),
		guest_NRADDR(state.regs),
		guest_SC_CLASS(state.regs),
		guest_GS_CONST(state.regs),
		guest_IP_AT_SYSCALL(state.regs)
	{

	}

};


class _VexGuestX86State :public Guest_State {
public:
    /* Event check fail addr and counter. */
    _X86State::host_EvC_FAILADDR  host_EvC_FAILADDR; /* 0 */
    _X86State::host_EvC_COUNTER host_EvC_COUNTER;  /* 4 */
    _X86State::guest_EAX guest_EAX;         /* 8 */
    _X86State::guest_ECX guest_ECX;
    _X86State::guest_EDX guest_EDX;
    _X86State::guest_EBX guest_EBX;
    _X86State::guest_ESP guest_ESP;
    _X86State::guest_EBP guest_EBP;
    _X86State::guest_ESI guest_ESI;
    _X86State::guest_EDI guest_EDI;         /* 36 */

    /* 4-word thunk used to calculate O S Z A C P flags. */
    _X86State::guest_CC_OP guest_CC_OP;       /* 40 */
    _X86State::guest_CC_DEP1 guest_CC_DEP1;
    _X86State::guest_CC_DEP2 guest_CC_DEP2;
    _X86State::guest_CC_NDEP guest_CC_NDEP;     /* 52 */
    /* The D flag is stored here, encoded as either -1 or +1 */
    _X86State::guest_DFLAG guest_DFLAG;       /* 56 */
    /* Bit 21 (ID) of eflags stored here, as either 0 or 1. */
    _X86State::guest_IDFLAG guest_IDFLAG;      /* 60 */
    /* Bit 18 (AC) of eflags stored here, as either 0 or 1. */
    _X86State::guest_ACFLAG guest_ACFLAG;      /* 64 */

    /* EIP */
    _X86State::guest_EIP guest_EIP;         /* 68 */

    /* FPU */
    _X86State::guest_FPREG guest_FPREG;    /* 72 */
    _X86State::guest_FPTAG guest_FPTAG;   /* 136 */
    _X86State::guest_FPROUND guest_FPROUND;    /* 144 */
    _X86State::guest_FC3210 guest_FC3210;     /* 148 */
    _X86State::guest_FTOP guest_FTOP;       /* 152 */

    /* SSE */
    _X86State::guest_SSEROUND guest_SSEROUND;   /* 156 */
    _X86State::guest_XMM0 guest_XMM0;       /* 160 */
    _X86State::guest_XMM1 guest_XMM1;
    _X86State::guest_XMM2 guest_XMM2;
    _X86State::guest_XMM3 guest_XMM3;
    _X86State::guest_XMM4 guest_XMM4;
    _X86State::guest_XMM5 guest_XMM5;
    _X86State::guest_XMM6 guest_XMM6;
    _X86State::guest_XMM7 guest_XMM7;

    /* Segment registers. */
    _X86State::guest_CS guest_CS;
    _X86State::guest_DS guest_DS;
    _X86State::guest_ES guest_ES;
    _X86State::guest_FS guest_FS;
    _X86State::guest_GS guest_GS;
    _X86State::guest_SS guest_SS;
    /* LDT/GDT stuff. */
    _X86State::guest_LDT guest_LDT; /* host addr, a VexGuestX86SegDescr* */
    _X86State::guest_GDT guest_GDT; /* host addr, a VexGuestX86SegDescr* */

    /* Emulation notes */
    _X86State::guest_EMNOTE guest_EMNOTE;

    /* For clflush/clinval: record start and length of area */
    _X86State::guest_CMSTART guest_CMSTART;
    _X86State::guest_CMLEN guest_CMLEN;

    /* Used to record the unredirected guest address at the start of
       a translation whose start has been redirected.  By reading
       this pseudo-register shortly afterwards, the translation can
       find out what the corresponding no-redirection address was.
       Note, this is only set for wrap-style redirects, not for
       replace-style ones. */
    _X86State::guest_NRADDR guest_NRADDR;

    /* Used for Darwin syscall dispatching. */
    _X86State::guest_SC_CLASS guest_SC_CLASS;

    /* Needed for Darwin (but mandated for all guest architectures):
       EIP at the last syscall insn (int 0x80/81/82, sysenter,
       syscall).  Used when backing up to restart a syscall that has
       been interrupted by a signal. */
    _X86State::guest_IP_AT_SYSCALL guest_IP_AT_SYSCALL;

    /* Padding to make it have an 16-aligned size */
    _X86State::padding1 padding1;
    _X86State::padding2 padding2;
    _X86State::padding3 padding3;
public:
    _VexGuestX86State(State &state) :
        Guest_State(state),
        host_EvC_FAILADDR(state.regs),
        host_EvC_COUNTER(state.regs),
        guest_EAX(state.regs),
        guest_ECX(state.regs),
        guest_EDX(state.regs),
        guest_EBX(state.regs),
        guest_ESP(state.regs),
        guest_EBP(state.regs),
        guest_ESI(state.regs),
        guest_EDI(state.regs),
        guest_CC_OP(state.regs),
        guest_CC_DEP1(state.regs),
        guest_CC_DEP2(state.regs),
        guest_CC_NDEP(state.regs),
        guest_DFLAG(state.regs),
        guest_IDFLAG(state.regs),
        guest_ACFLAG(state.regs),
        guest_EIP(state.regs),
        guest_FPREG(state.regs),
        guest_FPTAG(state.regs),
        guest_FPROUND(state.regs),
        guest_FC3210(state.regs),
        guest_FTOP(state.regs),
        guest_SSEROUND(state.regs),
        guest_XMM0(state.regs),
        guest_XMM1(state.regs),
        guest_XMM2(state.regs),
        guest_XMM3(state.regs),
        guest_XMM4(state.regs),
        guest_XMM5(state.regs),
        guest_XMM6(state.regs),
        guest_XMM7(state.regs),
        guest_CS(state.regs),
        guest_DS(state.regs),
        guest_ES(state.regs),
        guest_FS(state.regs),
        guest_GS(state.regs),
        guest_SS(state.regs),
        guest_LDT(state.regs),
        guest_GDT(state.regs),
        guest_EMNOTE(state.regs),
        guest_CMSTART(state.regs),
        guest_CMLEN(state.regs),
        guest_NRADDR(state.regs),
        guest_SC_CLASS(state.regs),
        guest_IP_AT_SYSCALL(state.regs),
        padding1(state.regs),
        padding2(state.regs),
        padding3(state.regs)
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

class _VexGuestX86SegDescr : public Guest_State {
public:
    class _Bits {
    public:
        _X86SegDescr::LimitLow LimitLow;
        _X86SegDescr::BaseLow BaseLow;
        _X86SegDescr::BaseMid BaseMid;
        _X86SegDescr::Type Type;
        _X86SegDescr::Dpl Dpl;
        _X86SegDescr::Pres Pres;
        _X86SegDescr::LimitHi LimitHi;
        _X86SegDescr::Sys Sys;
        _X86SegDescr::Reserved_0 Reserved_0;
        _X86SegDescr::Default_Big Default_Big;
        _X86SegDescr::Granularity Granularity;
        _X86SegDescr::BaseHi BaseHi;
        _Bits(State &state, ADDR base):
            LimitLow(state.mem, base + 0),
            BaseLow(state.mem, base + 2),
            BaseMid(state.mem, base + 4),
            Type(state.mem, base + 4),
            Dpl(state.mem, base + 4),
            Pres(state.mem, base + 4),
            LimitHi(state.mem, base + 4),
            Sys(state.mem, base + 4),
            Reserved_0(state.mem, base + 4),
            Default_Big(state.mem, base + 4),
            Granularity(state.mem, base + 4),
            BaseHi(state.mem, base + 4)
        {
        }
    };
    class _Words {
    public:
        _X86SegDescr::word1 word1;
        _X86SegDescr::word2 word2;
        _Words(State& state, ADDR base) :
            word1(state.mem, base),
            word2(state.mem, base + 4)
        {
        }
    };

    class _LdtEnt {
    public:
        _Words Words;
        _Bits Bits;
        _LdtEnt(State &state, ADDR base) :
            Words(state, base),
            Bits(state, base)
        {
        }
    };

    _LdtEnt LdtEnt;
    _VexGuestX86SegDescr(State &state, void* base) :
        Guest_State(state), 
        LdtEnt(state, (ADDR)base)
    {
    }
};

namespace Regs {
	using AMD64 = _VexGuestAMD64State;
    using X86 = _VexGuestX86State;
    using X86SegDescr = _VexGuestX86SegDescr;
}

#undef ISUNSIGNED_TYPE