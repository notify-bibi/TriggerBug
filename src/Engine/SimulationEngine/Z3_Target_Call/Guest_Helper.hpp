#pragma once


#include "../State_class.hpp"
#include "Z3_Target_Call.hpp"


static inline ULong resultsr(Vns const & retv) {
    Z3_inc_ref(retv, retv);
    ULong ret = (ULong)(Z3_ast)retv;
    if (ret & (~((1ull << 48) - 1))) {
        vex_printf("system error");
    }
    return (ret & ((1ull << 48) - 1)) | (0xfa1dull << 48);;
}
#define TRRET(retv) (retv.real()? (ULong)(retv):resultsr(retv))
#define ISUNSIGNED_TYPE(type) ((type)-1 > 0)

namespace hp{

    template<typename Type>
    class GM {
        Vns m_base;
        MEM& m_obj;
        template <typename T> friend class GMP;
        template <typename T, UInt shift, UInt bits> friend class GMW;

        GM(MEM& obj, Vns const& base) :
            m_obj(obj),
            m_base(base)
        {}

        GM(MEM& obj) :
            m_obj(obj),
            m_base(obj, (ADDR)0)
        {}

        GM(MEM& obj, ADDR base) :
            m_obj(obj),
            m_base(obj, base)
        {}

        template<typename T>
        GM(MEM& obj, T base) :
            m_obj(obj),
            m_base(obj, (ADDR)base)
        {}

        MEM& obj() const {
            return static_cast<MEM&>(m_obj);
        }

    public:

        /*Read{*/
        template<typename T>
        inline operator T () const {
            return (T)(Type)obj().Iex_Load<(IRType)(sizeof(Type) << 3)>(m_base);
        }

        inline operator Vns () const {
            return obj().Iex_Load<(IRType)(sizeof(Type) << 3)>(m_base);
        }
        /*}Read*/


        /*Write{*/
        template<typename T>
        inline void operator=(T const data) {
            obj().Ist_Store(m_base, (Type)data);
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
        /*}Write*/

        GMP<Type>& operator &() const {
            return *(GMP<Type>*)this;;
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


    template<typename Type>
    class GMP:private GM<Type> {
    public:
        GMP(MEM& obj, Vns const& base): GM<Type>(obj, base)
        {}

        GMP(MEM& obj) :GM<Type>(obj)
        {}

        GMP(MEM& obj, ADDR base) : GM<Type>(obj, base)
        {}

        template<typename T>
        GMP(MEM& obj, T base) :GM<Type>(obj, base)
        {}

        template<typename T>
        GMP(GMP<T> const &C) : GM<Type>(C.obj(), C.operator Vns())
        {}

        MEM& obj() const {
            return static_cast<MEM &>(m_obj);
        }

        template<typename T>
        inline operator T () const {
            return (T)m_base;
        }

        inline operator Vns () const {
            return m_base;
        }

        /*convert{*/
        template <typename T>
        inline operator GMP<T>& () {
            return static_cast<GMP<T>&>(*this);
        }
        /*}convert*/

        template<typename T>
        inline void operator=(T const data) {
            m_base = (ADDR)data;
        }

        inline void operator=(Vns const &data) {
            m_base = data;
        }


        inline GM<Type>& operator*() const {
            return *(GM<Type>*)this;
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


    template<typename Type>
    class GR {
        Register<REGISTER_LEN>& m_obj;
        UInt ir_o;
        template <typename T> friend class GRP;

    public:
        GR(Register<REGISTER_LEN>& obj, UInt iro) :
            m_obj(obj),
            ir_o(iro)
        {}

        Register<REGISTER_LEN>& obj() const {
            return static_cast<Register<REGISTER_LEN>&>(m_obj);
        }

    public:

        /*Read{*/
        template<typename T>
        inline operator T () const {
            return (T)(Type)obj().Iex_Get<(IRType)(sizeof(Type) << 3)>(ir_o);
        }

        inline operator Vns () const {
            return obj().Iex_Get<(IRType)(sizeof(Type) << 3)>(ir_o);
        }
        /*}Read*/


        /*Write{*/
        template<typename T>
        inline void operator=(T const data) {
            obj().Ist_Put(ir_o, (Type)data);
        }

        void operator=(Vns const& data) {
            if ((sizeof(Type) << 3) == data.bitn) {
                obj().Ist_Put(ir_o, data);
            }
            else if ((sizeof(Type) << 3) > data.bitn) {
                if (ISUNSIGNED_TYPE(Type)) {
                    obj().Ist_Put(ir_o, data.zext(data.bitn - (sizeof(Type) << 3)));
                }
                else {
                    obj().Ist_Put(ir_o, data.sext(data.bitn - (sizeof(Type) << 3)));
                }
            }
            else {
                obj().Ist_Put(ir_o, data.extract<(int)((sizeof(Type) << 3) - 1), 0>());
            }
        }
        /*}Write*/

        GRP<Type>& operator &() const {
            return *(GRP<Type>*)this;;
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


    template<typename Type>
    class GRP :private GR<Type> {
    public:
        GRP(Register<REGISTER_LEN>& obj, UInt iro) : GR<Type>(obj, iro)
        {}

        template<typename T>
        GRP(GRP<T> const& C) : GR<Type>(C.obj(), C.ir_o)
        {}

        Register<REGISTER_LEN>& obj() const {
            return static_cast<Register<REGISTER_LEN>&>(m_obj);
        }

        /*convert{*/
        template <typename T>
        inline operator GRP<T>& () {
            return static_cast<GRP<T>&>(*this);
        }
        /*}convert*/

        inline GR<Type>& operator*() const {
            return *(GR<Type>*)this;
        }


        inline GR<Type> operator [](UInt idx) {
            return GR<Type>(obj(), m_base + idx * (sizeof(Type)));
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


    template<typename Type, UInt shift = 0, UInt bits = (sizeof(Type) << 3)>
    class GMW :private GM<Type> {
    public:
        GMW(MEM& obj, Vns const& base) :GM(obj, base)
        {}

        GMW(MEM& obj) :GM(obj)
        {}

        GMW(MEM& obj, ADDR base) :GM(obj, base)
        {}

        template<typename T>
        GMW(MEM& obj, T base) : GM(obj, base)
        {}

        operator Vns() const {
            if (((sizeof(Type) << 3) == bits) && (shift == 0)) {
                return obj().Iex_Load<(sizeof(Type) << 3)>(m_base);
            }
            if (ISUNSIGNED_TYPE(Type)) {
                return ((GM<Type>*)this)->operator Vns().extract<(shift + bits - 1), shift>().zext((sizeof(Type) << 3) - bits);
            }
            else {
                return ((GM<Type>*)this)->operator Vns().extract<(shift + bits - 1), shift>().sext((sizeof(Type) << 3) - bits);
            }
        }
    };

};

using namespace hp;
using FloatP = GMP<Float>;
using DoubleP = GMP<Double>;

using BoolP = GMP<Bool>;
using UCharP = GMP<UChar>;
using SCharP = GMP<SChar>;
using CharP = GMP<SChar>;
using UShortP = GMP<UShort>;
using ShortP = GMP<SShort>;
using SShortP = GMP<SShort>;
using UIntP = GMP<UInt>;
using IntP = GMP<Int>;
using SIntP = GMP<Int>;
using ULongP = GMP<ULong>;
using SLongP = GMP<SLong>;
using LongP = GMP<SLong>;
using m128P = GMP<__m128i>;
using m256P = GMP<__m256i>;
using V256P = GMP<V256>;
using V128P = GMP<V128>;







class _VexGuestAMD64State {
public:
    /*0  */GR<ULong >  host_EvC_FAILADDR;
    /*8  */GR<UInt >   host_EvC_COUNTER;
    /*12 */GR<UInt >   pad0;
    /*16 */GR<ULong>   guest_RAX;
    /*24 */GR<ULong>   guest_RCX;
    /*32 */GR<ULong>   guest_RDX;
    /*40 */GR<ULong>   guest_RBX;
    /*48 */GR<ULong>   guest_RSP;
    /*56 */GR<ULong>   guest_RBP;
    /*64 */GR<ULong>   guest_RSI;
    /*72 */GR<ULong>   guest_RDI;
    /*80 */GR<ULong>   guest_R8;
    /*88 */GR<ULong>   guest_R9;
    /*96 */GR<ULong>   guest_R10;
    /*104*/GR<ULong>   guest_R11;
    /*112*/GR<ULong>   guest_R12;
    /*120*/GR<ULong>   guest_R13;
    /*128*/GR<ULong>   guest_R14;
    /*136*/GR<ULong>   guest_R15;
    /*144*/GR<ULong>   guest_CC_OP;
    /*152*/GR<ULong>   guest_CC_DEP1;
    /*160*/GR<ULong>   guest_CC_DEP2;
    /*168*/GR<ULong>   guest_CC_NDEP;
    /*176*/GR<ULong>   guest_DFLAG;
    /*184*/GR<ULong>   guest_RIP;
    /*192*/GR<ULong>   guest_ACFLAG;
    /*200*/GR<ULong>   guest_IDFLAG;
    /*208*/GR<ULong>   guest_FS_CONST;
    /*216*/GR<ULong>   guest_SSEROUND;
    /*224*/GR<__m256i> guest_YMM0;
    /*256*/GR<__m256i> guest_YMM1;
    /*288*/GR<__m256i> guest_YMM2;
    /*320*/GR<__m256i> guest_YMM3;
    /*352*/GR<__m256i> guest_YMM4;
    /*384*/GR<__m256i> guest_YMM5;
    /*416*/GR<__m256i> guest_YMM6;
    /*448*/GR<__m256i> guest_YMM7;
    /*480*/GR<__m256i> guest_YMM8;
    /*512*/GR<__m256i> guest_YMM9;
    /*544*/GR<__m256i> guest_YMM10;
    /*576*/GR<__m256i> guest_YMM11;
    /*608*/GR<__m256i> guest_YMM12;
    /*640*/GR<__m256i> guest_YMM13;
    /*672*/GR<__m256i> guest_YMM14;
    /*704*/GR<__m256i> guest_YMM15;
    /*736*/GR<__m256i> guest_YMM16;
    /*768*/GR<UInt>    guest_FTOP;
    /*772*/GR<UInt>    pad1;
    /*776*/GRP<ULong>  guest_FPREG;
    /*840*/GRP<UChar>  guest_FPTAG;
    /*848*/GR<ULong>   guest_FPROUND;
    /*856*/GR<ULong>   guest_FC3210;
    /*864*/GR<UInt>    guest_EMNOTE;
    /*868*/GR<UInt>    pad2;
    /*872*/GR<ULong>   guest_CMSTART;
    /*880*/GR<ULong>   guest_CMLEN;
    /*888*/GR<ULong>   guest_NRADDR;
    /*896*/GR<ULong>   guest_SC_CLASS;
    /*904*/GR<ULong>   guest_GS_CONST;
    /*912*/GR<ULong>   guest_IP_AT_SYSCALL;
    State& m_state;
public:
	_VexGuestAMD64State(State &s):
        m_state(s),
        host_EvC_FAILADDR   (s,0  ),
        host_EvC_COUNTER    (s,8  ),
        pad0                (s,12 ),
        guest_RAX           (s,16 ),
        guest_RCX           (s,24 ),
        guest_RDX           (s,32 ),
        guest_RBX           (s,40 ),
        guest_RSP           (s,48 ),
        guest_RBP           (s,56 ),
        guest_RSI           (s,64 ),
        guest_RDI           (s,72 ),
        guest_R8            (s,80 ),
        guest_R9            (s,88 ),
        guest_R10           (s,96 ),
        guest_R11           (s,104),
        guest_R12           (s,112),
        guest_R13           (s,120),
        guest_R14           (s,128),
        guest_R15           (s,136),
        guest_CC_OP         (s,144),
        guest_CC_DEP1       (s,152),
        guest_CC_DEP2       (s,160),
        guest_CC_NDEP       (s,168),
        guest_DFLAG         (s,176),
        guest_RIP           (s,184),
        guest_ACFLAG        (s,192),
        guest_IDFLAG        (s,200),
        guest_FS_CONST      (s,208),
        guest_SSEROUND      (s,216),
        guest_YMM0          (s,224),
        guest_YMM1          (s,256),
        guest_YMM2          (s,288),
        guest_YMM3          (s,320),
        guest_YMM4          (s,352),
        guest_YMM5          (s,384),
        guest_YMM6          (s,416),
        guest_YMM7          (s,448),
        guest_YMM8          (s,480),
        guest_YMM9          (s,512),
        guest_YMM10         (s,544),
        guest_YMM11         (s,576),
        guest_YMM12         (s,608),
        guest_YMM13         (s,640),
        guest_YMM14         (s,672),
        guest_YMM15         (s,704),
        guest_YMM16         (s,736),
        guest_FTOP          (s,768),
        pad1                (s,772),
        guest_FPREG         (s,776),
        guest_FPTAG         (s,840),
        guest_FPROUND       (s,848),
        guest_FC3210        (s,856),
        guest_EMNOTE        (s,864),
        pad2                (s,868),
        guest_CMSTART       (s,872),
        guest_CMLEN         (s,880),
        guest_NRADDR        (s,888),
        guest_SC_CLASS      (s,896),
        guest_GS_CONST      (s,904),
        guest_IP_AT_SYSCALL (s,912)
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

    /*0  */GR<UInt>      host_EvC_FAILADDR;
    /*4  */GR<UInt>      host_EvC_COUNTER;
    /*8  */GR<UInt>      guest_EAX;
    /*12 */GR<UInt>      guest_ECX;
    /*16 */GR<UInt>      guest_EDX;
    /*20 */GR<UInt>      guest_EBX;
    /*24 */GR<UInt>      guest_ESP;
    /*28 */GR<UInt>      guest_EBP;
    /*32 */GR<UInt>      guest_ESI;
    /*36 */GR<UInt>      guest_EDI;
    /*40 */GR<UInt>      guest_CC_OP;
    /*44 */GR<UInt>      guest_CC_DEP1;
    /*48 */GR<UInt>      guest_CC_DEP2;
    /*52 */GR<UInt>      guest_CC_NDEP;
    /*56 */GR<UInt>      guest_DFLAG;
    /*60 */GR<UInt>      guest_IDFLAG;
    /*64 */GR<UInt>      guest_ACFLAG;
    /*68 */GR<UInt>      guest_EIP;
    /*72 */GRP<ULong>    guest_FPREG;
    /*136*/GRP<UChar>    guest_FPTAG;
    /*144*/GR<UInt>      guest_FPROUND;
    /*148*/GR<UInt>      guest_FC3210;
    /*152*/GR<UInt>      guest_FTOP;
    /*156*/GR<UInt>      guest_SSEROUND;
    /*160*/GR<U128>      guest_XMM0;
    /*176*/GR<U128>      guest_XMM1;
    /*192*/GR<U128>      guest_XMM2;
    /*208*/GR<U128>      guest_XMM3;
    /*224*/GR<U128>      guest_XMM4;
    /*240*/GR<U128>      guest_XMM5;
    /*256*/GR<U128>      guest_XMM6;
    /*272*/GR<U128>      guest_XMM7;
    /*288*/GR<UShort>    guest_CS;
    /*290*/GR<UShort>    guest_DS;
    /*292*/GR<UShort>    guest_ES;
    /*294*/GR<UShort>    guest_FS;
    /*296*/GR<UShort>    guest_GS;
    /*298*/GR<UShort>    guest_SS;
    /*304*/GR<ULong>     guest_LDT;
    /*312*/GR<ULong>     guest_GDT;
    /*320*/GR<UInt>      guest_EMNOTE;
    /*324*/GR<UInt>      guest_CMSTART;
    /*328*/GR<UInt>      guest_CMLEN;
    /*332*/GR<UInt>      guest_NRADDR;
    /*336*/GR<UInt>      guest_SC_CLASS;
    /*340*/GR<UInt>      guest_IP_AT_SYSCALL;
    /*344*/GR<UInt>      padding1;
    /*348*/GR<UInt>      padding2;
    /*352*/GR<UInt>      padding3;
public:
    _VexGuestX86State(State& s):
        host_EvC_FAILADDR   (s, 0  ),
        host_EvC_COUNTER    (s, 4  ),
        guest_EAX           (s, 8  ),
        guest_ECX           (s, 12 ),
        guest_EDX           (s, 16 ),
        guest_EBX           (s, 20 ),
        guest_ESP           (s, 24 ),
        guest_EBP           (s, 28 ),
        guest_ESI           (s, 32 ),
        guest_EDI           (s, 36 ),
        guest_CC_OP         (s, 40 ),
        guest_CC_DEP1       (s, 44 ),
        guest_CC_DEP2       (s, 48 ),
        guest_CC_NDEP       (s, 52 ),
        guest_DFLAG         (s, 56 ),
        guest_IDFLAG        (s, 60 ),
        guest_ACFLAG        (s, 64 ),
        guest_EIP           (s, 68 ),
        guest_FPREG         (s, 72 ),
        guest_FPTAG         (s, 136),
        guest_FPROUND       (s, 144),
        guest_FC3210        (s, 148),
        guest_FTOP          (s, 152),
        guest_SSEROUND      (s, 156),
        guest_XMM0          (s, 160),
        guest_XMM1          (s, 176),
        guest_XMM2          (s, 192),
        guest_XMM3          (s, 208),
        guest_XMM4          (s, 224),
        guest_XMM5          (s, 240),
        guest_XMM6          (s, 256),
        guest_XMM7          (s, 272),
        guest_CS            (s, 288),
        guest_DS            (s, 290),
        guest_ES            (s, 292),
        guest_FS            (s, 294),
        guest_GS            (s, 296),
        guest_SS            (s, 298),
        guest_LDT           (s, 304),
        guest_GDT           (s, 312),
        guest_EMNOTE        (s, 320),
        guest_CMSTART       (s, 324),
        guest_CMLEN         (s, 328),
        guest_NRADDR        (s, 332),
        guest_SC_CLASS      (s, 336),
        guest_IP_AT_SYSCALL (s, 340),
        padding1            (s, 344),
        padding2            (s, 348),
        padding3            (s, 352)
    {

    }

};

namespace _X86SegDescr {
    using LimitLow =    GMW<UShort>;
    using BaseLow =     GMW<UShort>;
    using BaseMid =     GMW<UInt, 0, 8>;
    using Type =        GMW<UInt, 8, 5>;
    using Dpl =         GMW<UInt, 13, 2>;
    using Pres =        GMW<UInt, 15, 1>;
    using LimitHi =     GMW<UInt, 16, 4>;
    using Sys =         GMW<UInt, 20, 1>;
    using Reserved_0 =  GMW<UInt, 21, 1>;
    using Default_Big = GMW<UInt, 22, 1>;
    using Granularity = GMW<UInt, 23, 1>;
    using BaseHi =      GMW<UInt, 24, 8>;
    using word1 =       GMW<UInt>;
    using word2 =       GMW<UInt>;
}

class _VexGuestX86SegDescr {
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
        LdtEnt(state, (ADDR)base)
    {

    }
};

namespace Regs {
	using AMD64 = _VexGuestAMD64State;
    using X86 = _VexGuestX86State;
    //using X86SegDescr = _VexGuestX86SegDescr;
}

#undef ISUNSIGNED_TYPE