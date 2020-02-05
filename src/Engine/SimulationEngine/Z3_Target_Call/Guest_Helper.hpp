#pragma once
#include "../State_class.hpp"
#include "Z3_Target_Call.hpp"


#define ISUNSIGNED_TYPE(type) ((type)-1 > 0)

namespace TRGL{
class VexGuestAMD64State;
class VexGuestX86SegDescr;
class VexGuestX86State;
}


namespace hp{

    template<typename ADDR, typename Type>
    class GM {
        Vns m_base;
        MEM<ADDR>& m_obj;
        template <typename ADDR, typename T> friend class GMP;
        template <typename ADDR, typename T, UInt shift, UInt bits> friend class GMW;
        friend class TRGL::VexGuestAMD64State;
        friend class TRGL::VexGuestX86SegDescr;
        friend class TRGL::VexGuestX86State;

        GM(MEM<ADDR>& obj, Vns const& base) :
            m_obj(obj),
            m_base(base)
        {}

        GM(MEM<ADDR>& obj) :
            m_obj(obj),
            m_base(obj, (ADDR)0)
        {}

        GM(MEM<ADDR>& obj, ADDR base) :
            m_obj(obj),
            m_base(obj, base)
        {}

        template<typename T>
        GM(MEM<ADDR>& obj, T base) :
            m_obj(obj),
            m_base(obj, (ADDR)base)
        {}

        MEM<ADDR>& obj() const {
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
        inline T operator=(T const data) {
            obj().Ist_Store(m_base, (Type)data);
            return data;
        }

        inline Vns const&  operator=(Vns const& data) {
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
            return data;
        }
        /*}Write*/

        GMP<ADDR, Type>& operator &() const {
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
        inline GM(GMP<ADDR, T> const&) = delete;
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

    /*
        GMP<UChar> ps = &x87_state.reg[0];  ok
        UChar* p = &x87_state.reg[0];       err
    */
    template<typename ADDR, typename Type>
    class GMP:private GM<ADDR, Type> {
    public:
        GMP(MEM<ADDR>& obj, Vns const& base): GM<ADDR, Type>(obj, base)
        {}

        GMP(MEM<ADDR>& obj) :GM<ADDR, Type>(obj)
        {}

        GMP(MEM<ADDR>& obj, ADDR base) : GM<ADDR, Type>(obj, base)
        {}

        template<typename T>
        GMP(MEM<ADDR>& obj, T base) :GM<ADDR, Type>(obj, base)
        {}

        template<typename T>
        GMP(GMP<ADDR, T> const &C) : GM<ADDR, Type>(C.obj(), ((GM<ADDR, T>&)C).m_base)
        {}

        /*template<typename T>
        GMP(GM<T> const& C) : GM<Type>(C)
        {}*/

        MEM<ADDR>& obj() const {
            return static_cast<MEM<ADDR>&>(m_obj);
        }

        /*template<typename T>
        inline operator T () const {
            return (T)m_base;
        }*/


        /*convert{*/
        template <typename T>
        inline operator GMP<ADDR, T>& () {
            return static_cast<GMP<ADDR, T>&>(*this);
        }
        /*}convert*/

        template<typename T>
        inline void operator=(T const data) {
            m_base = (ADDR)data;
        }

        inline void operator=(Vns const &data) {
            m_base = data;
        }


        inline GM<ADDR, Type>& operator*() const {
            return *(GM<ADDR, Type>*)this;
        }


        inline GM<ADDR, Type> operator [](UInt idx) {
            return GM<ADDR, Type>(obj(), m_base + idx * (sizeof(Type)));
        }



    #define REG_OPERATOR(op)					\
		    template<typename _dataType>		\
		    inline GMP<ADDR, ype> operator op(_dataType data) const{\
			    return GMP<ADDR, Type>(obj(), m_base + data * (sizeof(Type)));	\
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
        inline GMP(GM<ADDR, T> const&) = delete;

        /*Read{*/
        template<typename T>
        inline operator T () const = delete;
        inline operator Vns () const = delete;
        /*}Read*/

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


    template<typename ADDR, typename Type>
    class GR {
        template <typename ADDR, typename T> friend class GRP;
        friend class TRGL::VexGuestAMD64State;
        friend class TRGL::VexGuestX86SegDescr;
        friend class TRGL::VexGuestX86State;
        Register<REGISTER_LEN>& m_obj;
        UInt ir_o;
        GR(Register<REGISTER_LEN>& obj, UInt iro) :
            m_obj(obj),
            ir_o(iro)
        {}

    public:
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
        inline T operator=(T const data) {
            obj().Ist_Put(ir_o, (Type)data);
            return data;
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

        GRP<ADDR, Type>& operator &() const {
            return *(GRP<ADDR, Type>*)this;;
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
        inline GR(GR<ADDR, T> const &) = delete;

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


    template<typename ADDR, typename Type>
    class GRP :private GR<ADDR, Type> {
    public:
        GRP(Register<REGISTER_LEN>& obj, UInt iro) : GR<ADDR, Type>(obj, iro)
        {}

        template<typename T>
        GRP(GRP<ADDR, T> const& C) : GR<ADDR, Type>(C.obj(), ((GR<ADDR, T>&)C).ir_o)
        {}

        Register<REGISTER_LEN>& obj() const {
            return static_cast<Register<REGISTER_LEN>&>(m_obj);
        }

        /*convert{*/
        template <typename T>
        inline operator GRP<ADDR, T>& () {
            return static_cast<GRP<ADDR, T>&>(*this);
        }
        /*}convert*/

        inline GR<ADDR, Type>& operator*() const {
            return *(GR<ADDR, Type>*)this;
        }


        inline GR<ADDR, Type> operator [](UInt idx) {
            return GR<ADDR, Type>(obj(), ir_o + idx * (sizeof(Type)));
        }

    #define REG_OPERATOR(op)					\
		    template<typename _dataType>		\
		    inline GR<ADDR, Type> operator op(_dataType offset) const{\
			    return GR<ADDR, Type>(obj(), ir_o + offset * (sizeof(Type)));	\
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
        inline GRP(GR<ADDR, T> const&) = delete;

        template<typename T>
        inline operator T () const = delete;

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


    template<typename ADDR, typename Type, UInt shift = 0, UInt bits = (sizeof(Type) << 3)>
    class GMW :private GM<ADDR, Type> {
    public:
        GMW(MEM<ADDR>& obj, Vns const& base) :GM(obj, base)
        {}

        GMW(MEM<ADDR>& obj) :GM(obj)
        {}

        GMW(MEM<ADDR>& obj, ADDR base) :GM(obj, base)
        {}

        template<typename T>
        GMW(MEM<ADDR>& obj, T base) : GM(obj, base)
        {}

        operator Vns() const {
            if (((sizeof(Type) << 3) == bits) && (shift == 0)) {
                return ((GM<Type>*)this)->operator Vns();
            }
            if (ISUNSIGNED_TYPE(Type)) {
                return ((GM<Type>*)this)->operator Vns().extract<(shift + bits - 1), shift>().zext((sizeof(Type) << 3) - bits);
            }
            else {
                return ((GM<Type>*)this)->operator Vns().extract<(shift + bits - 1), shift>().sext((sizeof(Type) << 3) - bits);
            }
        }

        template<typename T>
        inline operator T () const {
            return (T)(Type)this->operator Vns();
        }
    };

};

using namespace hp;



namespace TRGL {

class VexGuestAMD64State {
public:
    /*0  */GR<Addr64, ULong >  host_EvC_FAILADDR;
    /*8  */GR<Addr64, UInt >   host_EvC_COUNTER;
    /*12 */GR<Addr64, UInt >   pad0;
    /*16 */GR<Addr64, ULong>   guest_RAX;
    /*24 */GR<Addr64, ULong>   guest_RCX;
    /*32 */GR<Addr64, ULong>   guest_RDX;
    /*40 */GR<Addr64, ULong>   guest_RBX;
    /*48 */GR<Addr64, ULong>   guest_RSP;
    /*56 */GR<Addr64, ULong>   guest_RBP;
    /*64 */GR<Addr64, ULong>   guest_RSI;
    /*72 */GR<Addr64, ULong>   guest_RDI;
    /*80 */GR<Addr64, ULong>   guest_R8;
    /*88 */GR<Addr64, ULong>   guest_R9;
    /*96 */GR<Addr64, ULong>   guest_R10;
    /*104*/GR<Addr64, ULong>   guest_R11;
    /*112*/GR<Addr64, ULong>   guest_R12;
    /*120*/GR<Addr64, ULong>   guest_R13;
    /*128*/GR<Addr64, ULong>   guest_R14;
    /*136*/GR<Addr64, ULong>   guest_R15;
    /*144*/GR<Addr64, ULong>   guest_CC_OP;
    /*152*/GR<Addr64, ULong>   guest_CC_DEP1;
    /*160*/GR<Addr64, ULong>   guest_CC_DEP2;
    /*168*/GR<Addr64, ULong>   guest_CC_NDEP;
    /*176*/GR<Addr64, ULong>   guest_DFLAG;
    /*184*/GR<Addr64, ULong>   guest_RIP;
    /*192*/GR<Addr64, ULong>   guest_ACFLAG;
    /*200*/GR<Addr64, ULong>   guest_IDFLAG;
    /*208*/GR<Addr64, ULong>   guest_FS_CONST;
    /*216*/GR<Addr64, ULong>   guest_SSEROUND;
    /*224*/GR<Addr64, __m256i> guest_YMM0;
    /*256*/GR<Addr64, __m256i> guest_YMM1;
    /*288*/GR<Addr64, __m256i> guest_YMM2;
    /*320*/GR<Addr64, __m256i> guest_YMM3;
    /*352*/GR<Addr64, __m256i> guest_YMM4;
    /*384*/GR<Addr64, __m256i> guest_YMM5;
    /*416*/GR<Addr64, __m256i> guest_YMM6;
    /*448*/GR<Addr64, __m256i> guest_YMM7;
    /*480*/GR<Addr64, __m256i> guest_YMM8;
    /*512*/GR<Addr64, __m256i> guest_YMM9;
    /*544*/GR<Addr64, __m256i> guest_YMM10;
    /*576*/GR<Addr64, __m256i> guest_YMM11;
    /*608*/GR<Addr64, __m256i> guest_YMM12;
    /*640*/GR<Addr64, __m256i> guest_YMM13;
    /*672*/GR<Addr64, __m256i> guest_YMM14;
    /*704*/GR<Addr64, __m256i> guest_YMM15;
    /*736*/GR<Addr64, __m256i> guest_YMM16;
    /*768*/GR<Addr64, UInt>    guest_FTOP;
    /*772*/GR<Addr64, UInt>    pad1;
    /*776*/GRP<Addr64, ULong>  guest_FPREG;
    /*840*/GRP<Addr64, UChar>  guest_FPTAG;
    /*848*/GR<Addr64, ULong>   guest_FPROUND;
    /*856*/GR<Addr64, ULong>   guest_FC3210;
    /*864*/GR<Addr64, UInt>    guest_EMNOTE;
    /*868*/GR<Addr64, UInt>    pad2;
    /*872*/GR<Addr64, ULong>   guest_CMSTART;
    /*880*/GR<Addr64, ULong>   guest_CMLEN;
    /*888*/GR<Addr64, ULong>   guest_NRADDR;
    /*896*/GR<Addr64, ULong>   guest_SC_CLASS;
    /*904*/GR<Addr64, ULong>   guest_GS_CONST;
    /*912*/GR<Addr64, ULong>   guest_IP_AT_SYSCALL;
    State<Addr64>& m_state;
public:
    VexGuestAMD64State() :VexGuestAMD64State(*(State<Addr64>*)g_state){}
	VexGuestAMD64State(State<Addr64>&s):
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

    inline operator MEM<Addr64>&() {
        return m_state.mem;
    }
};


class VexGuestX86State {
public:

    /*0  */GR<Addr32, UInt>      host_EvC_FAILADDR;
    /*4  */GR<Addr32, UInt>      host_EvC_COUNTER;
    /*8  */GR<Addr32, UInt>      guest_EAX;
    /*12 */GR<Addr32, UInt>      guest_ECX;
    /*16 */GR<Addr32, UInt>      guest_EDX;
    /*20 */GR<Addr32, UInt>      guest_EBX;
    /*24 */GR<Addr32, UInt>      guest_ESP;
    /*28 */GR<Addr32, UInt>      guest_EBP;
    /*32 */GR<Addr32, UInt>      guest_ESI;
    /*36 */GR<Addr32, UInt>      guest_EDI;
    /*40 */GR<Addr32, UInt>      guest_CC_OP;
    /*44 */GR<Addr32, UInt>      guest_CC_DEP1;
    /*48 */GR<Addr32, UInt>      guest_CC_DEP2;
    /*52 */GR<Addr32, UInt>      guest_CC_NDEP;
    /*56 */GR<Addr32, UInt>      guest_DFLAG;
    /*60 */GR<Addr32, UInt>      guest_IDFLAG;
    /*64 */GR<Addr32, UInt>      guest_ACFLAG;
    /*68 */GR<Addr32, UInt>      guest_EIP;
    /*72 */GRP<Addr32, ULong>    guest_FPREG;
    /*136*/GRP<Addr32, UChar>    guest_FPTAG;
    /*144*/GR<Addr32, UInt>      guest_FPROUND;
    /*148*/GR<Addr32, UInt>      guest_FC3210;
    /*152*/GR<Addr32, UInt>      guest_FTOP;
    /*156*/GR<Addr32, UInt>      guest_SSEROUND;
    /*160*/GR<Addr32, U128>      guest_XMM0;
    /*176*/GR<Addr32, U128>      guest_XMM1;
    /*192*/GR<Addr32, U128>      guest_XMM2;
    /*208*/GR<Addr32, U128>      guest_XMM3;
    /*224*/GR<Addr32, U128>      guest_XMM4;
    /*240*/GR<Addr32, U128>      guest_XMM5;
    /*256*/GR<Addr32, U128>      guest_XMM6;
    /*272*/GR<Addr32, U128>      guest_XMM7;
    /*288*/GR<Addr32, UShort>    guest_CS;
    /*290*/GR<Addr32, UShort>    guest_DS;
    /*292*/GR<Addr32, UShort>    guest_ES;
    /*294*/GR<Addr32, UShort>    guest_FS;
    /*296*/GR<Addr32, UShort>    guest_GS;
    /*298*/GR<Addr32, UShort>    guest_SS;
    /*304*/GR<Addr32, ULong>     guest_LDT;
    /*312*/GR<Addr32, ULong>     guest_GDT;
    /*320*/GR<Addr32, UInt>      guest_EMNOTE;
    /*324*/GR<Addr32, UInt>      guest_CMSTART;
    /*328*/GR<Addr32, UInt>      guest_CMLEN;
    /*332*/GR<Addr32, UInt>      guest_NRADDR;
    /*336*/GR<Addr32, UInt>      guest_SC_CLASS;
    /*340*/GR<Addr32, UInt>      guest_IP_AT_SYSCALL;
    /*344*/GR<Addr32, UInt>      padding1;
    /*348*/GR<Addr32, UInt>      padding2;
    /*352*/GR<Addr32, UInt>      padding3;
public:
    VexGuestX86State() :VexGuestX86State(*(State<Addr32>*)g_state) {}
    VexGuestX86State(State<Addr32>& s):
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

namespace X86SegDescr {
    using LimitLow =    GMW<Addr32, UShort>;
    using BaseLow =     GMW<Addr32, UShort>;
    using BaseMid =     GMW<Addr32, UInt, 0, 8>;
    using Type =        GMW<Addr32, UInt, 8, 5>;
    using Dpl =         GMW<Addr32, UInt, 13, 2>;
    using Pres =        GMW<Addr32, UInt, 15, 1>;
    using LimitHi =     GMW<Addr32, UInt, 16, 4>;
    using Sys =         GMW<Addr32, UInt, 20, 1>;
    using Reserved_0 =  GMW<Addr32, UInt, 21, 1>;
    using Default_Big = GMW<Addr32, UInt, 22, 1>;
    using Granularity = GMW<Addr32, UInt, 23, 1>;
    using BaseHi =      GMW<Addr32, UInt, 24, 8>;
    using word1 =       GMW<Addr32, UInt>;
    using word2 =       GMW<Addr32, UInt>;
}
//TriggerBug Guest Layout

    class VexGuestX86SegDescr {
    public:
        class Bits {
        public:
            X86SegDescr::LimitLow LimitLow;
            X86SegDescr::BaseLow BaseLow;
            X86SegDescr::BaseMid BaseMid;
            X86SegDescr::Type Type;
            X86SegDescr::Dpl Dpl;
            X86SegDescr::Pres Pres;
            X86SegDescr::LimitHi LimitHi;
            X86SegDescr::Sys Sys;
            X86SegDescr::Reserved_0 Reserved_0;
            X86SegDescr::Default_Big Default_Big;
            X86SegDescr::Granularity Granularity;
            X86SegDescr::BaseHi BaseHi;
            Bits(State<Addr32>& state, Addr32 base) :
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
        class Words {
        public:
            X86SegDescr::word1 word1;
            X86SegDescr::word2 word2;
            Words(State<Addr32>& state, Addr32 base) :
                word1(state.mem, base),
                word2(state.mem, base + 4)
            {
            }
        };

        class LdtEnt {
        public:
            Words Words;
            Bits Bits;
            LdtEnt(State<Addr32>& state, Addr32 base) :
                Words(state, base),
                Bits(state, base)
            {
            }
        };

        LdtEnt LdtEnt;
        VexGuestX86SegDescr(State<Addr32>& state, Addr32 base) :
            LdtEnt(state, base)
        {

        }
        VexGuestX86SegDescr(Addr32 base) :
            LdtEnt(*(State<Addr32>*)g_state, base)
        {

        }

    };
};

namespace Regs {
	using AMD64 = TRGL::VexGuestAMD64State;
    using X86 = TRGL::VexGuestX86State;
    //using X86SegDescr = _VexGuestX86SegDescr;
}

#undef ISUNSIGNED_TYPE