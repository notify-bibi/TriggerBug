#pragma once
#include "engine.hpp"


namespace helper {

	template<class _object, typename _PointerType = UChar, int offset = -1>
	class Pointer;
	class _VexGuestAMD64State;

	template<typename _PoinerType>
	void operator_set(MEM &obj, Vns const &_where, _PoinerType data) {
		obj.Ist_Store(_where, data);
	}
	
	template<int maxlength,typename _PoinerType>
	void operator_set(Register<maxlength> &obj, Vns const &_where, _PoinerType data) {
		assert(_where.real());
		obj.Ist_Put(_where, data);
	}

	void operator_set(MEM &obj, Vns const &_where, Vns const &data) {
		obj.Ist_Store(_where, data);
	}

	template<int maxlength>
	void operator_set(Register<maxlength> &obj, Vns const &_where, Vns const &data) {
		assert(_where.real());
		obj.Ist_Put(_where, data);
	}


	template<int bitn>
	Vns operator_get(MEM &obj, Vns const &_where) {
		return obj.Iex_Load<((IRType)bitn)>(_where);
	}

	template<int bitn>
	Vns  operator_get(Register<1000> &obj, Vns const &_where) {
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




	template<class _object, typename _PointerType = UChar, int offset = -1>
	class inPointer {
		template<class __object, typename __PointerType = UChar, int _offset = -1>
		friend class Pointer;
		friend class _VexGuestAMD64State;
	public:
		_object*m_obj;
		Vns		m_point;
		UShort	m_step;


		inline inPointer(_object &obj, Addr64 _p) :
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
			return operator_get<(sizeof(_PointerType) << 3)>(operator _object& (), this->m_point);
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




#undef inPointer_operator
	private:
		operator z3::expr()  = delete;
		operator z3::expr&()  = delete;
		operator const z3::expr() = delete;
		operator const z3::expr&() = delete;

	};




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


class _VexGuestAMD64State {
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
	template<int maxlength>
	_VexGuestAMD64State(Register<maxlength> &obj):
		host_EvC_FAILADDR(obj),
		host_EvC_COUNTER(obj),
		pad0(obj),
		pad1(obj),
		pad2(obj),
		guest_RAX(obj),
		guest_RCX(obj),
		guest_RDX(obj),
		guest_RBX(obj),
		guest_RSP(obj),
		guest_RBP(obj),
		guest_RSI(obj),
		guest_RDI(obj),
		guest_R8(obj),
		guest_R9(obj),
		guest_R10(obj),
		guest_R11(obj),
		guest_R12(obj),
		guest_R13(obj),
		guest_R14(obj),
		guest_R15(obj),
		guest_CC_OP(obj),
		guest_CC_DEP1(obj),
		guest_CC_DEP2(obj),
		guest_CC_NDEP(obj),
		guest_DFLAG(obj),
		guest_RIP(obj),
		guest_ACFLAG(obj),
		guest_IDFLAG(obj),
		guest_FS_CONST(obj),
		guest_SSEROUND(obj),
		guest_YMM0(obj),
		guest_YMM1(obj),
		guest_YMM2(obj),
		guest_YMM3(obj),
		guest_YMM4(obj),
		guest_YMM5(obj),
		guest_YMM6(obj),
		guest_YMM7(obj),
		guest_YMM8(obj),
		guest_YMM9(obj),
		guest_YMM10(obj),
		guest_YMM11(obj),
		guest_YMM12(obj),
		guest_YMM13(obj),
		guest_YMM14(obj),
		guest_YMM15(obj),
		guest_YMM16(obj),
		guest_FTOP(obj),
		guest_FPREG(obj),
		guest_FPTAG(obj),
		guest_FPROUND(obj),
		guest_FC3210(obj),
		guest_EMNOTE(obj),
		guest_CMSTART(obj),
		guest_CMLEN(obj),
		guest_NRADDR(obj),
		guest_SC_CLASS(obj),
		guest_GS_CONST(obj),
		guest_IP_AT_SYSCALL(obj)
	{

	}

};



namespace Regs {
	using AMD64 = _VexGuestAMD64State;
}

#undef ISUNSIGNED_TYPE