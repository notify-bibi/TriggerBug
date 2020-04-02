//#pragma once
//#include "state_class.h"
//#include "z3_target_call/z3_target_call.h"
//
//
//#define ISUNSIGNED_TYPE(type) ((type)-1 > 0)
//
//namespace TRGL{
//class VexGuestAMD64State;
//class VexGuestX86SegDescr;
//class VexGuestX86State;
//}
//
//
//namespace hp{
//
//    template<typename ADDR, typename Type>
//    class GM {
//        Vns m_base;
//        TR::MEM<ADDR>& m_obj;
//        template <typename ADDR, typename T> friend class GMP;
//        template <typename ADDR, typename T, UInt shift, UInt bits> friend class GMW;
//        friend class TRGL::VexGuestAMD64State;
//        friend class TRGL::VexGuestX86SegDescr;
//        friend class TRGL::VexGuestX86State;
//
//        GM(TR::MEM<ADDR>& obj, Vns const& base) :
//            m_obj(obj),
//            m_base(base)
//        {}
//
//        GM(TR::MEM<ADDR>& obj) :
//            m_obj(obj),
//            m_base(obj, (ADDR)0)
//        {}
//
//        GM(TR::MEM<ADDR>& obj, ADDR base) :
//            m_obj(obj),
//            m_base(obj, base)
//        {}
//
//        template<typename T>
//        GM(TR::MEM<ADDR>& obj, T base) :
//            m_obj(obj),
//            m_base(obj, (ADDR)base)
//        {}
//
//        TR::MEM<ADDR>& obj() const {
//            return static_cast<MEM&>(m_obj);
//        }
//
//
//    public:
//        /*Read{*/
//        template<typename T>
//        inline operator T () const {
//            return (T)(Type)obj().Iex_Load<(IRType)(sizeof(Type) << 3)>(m_base);
//        }
//
//        inline operator Vns () const {
//            return obj().Iex_Load<(IRType)(sizeof(Type) << 3)>(m_base);
//        }
//        /*}Read*/
//
//
//        /*Write{*/
//        template<typename T>
//        inline T operator=(T const data) {
//            obj().Ist_Store(m_base, (Type)data);
//            return data;
//        }
//
//        inline Vns const&  operator=(Vns const& data) {
//            if ((sizeof(Type) << 3) == data.bitn) {
//                obj().Ist_Store(m_base, data);
//            }
//            else if ((sizeof(Type) << 3) > data.bitn) {
//                if (ISUNSIGNED_TYPE(Type)) {
//                    obj().Ist_Store(m_base, data.zext(data.bitn - (sizeof(Type) << 3)));
//                }
//                else {
//                   obj().Ist_Store( m_base, data.sext(data.bitn - (sizeof(Type) << 3)));
//                }
//            }
//            else {
//                obj().Ist_Store(m_base, data.extract<(int)((sizeof(Type) << 3) - 1), 0>());
//            }
//            return data;
//        }
//        /*}Write*/
//
//        GMP<ADDR, Type>& operator &() const {
//            return *(GMP<Type>*)this;;
//        }
//
//
//
//    #define REG_OPERATOR(op)					\
//		    template<typename _dataType>		\
//		    Vns operator op(_dataType data) const{\
//			    return operator Vns() op data;	\
//		    }
//
//        REG_OPERATOR(+);
//        REG_OPERATOR(-);
//        REG_OPERATOR(*);
//        REG_OPERATOR(/ );
//        REG_OPERATOR(>> );
//        REG_OPERATOR(<< );
//        REG_OPERATOR(| );
//        REG_OPERATOR(&);
//        REG_OPERATOR(== );
//
//    #undef REG_OPERATOR
//
//    private:
//        template<typename T>
//        inline GM(GMP<ADDR, T> const&) = delete;
//        template<typename T>
//        T operator &() = delete;
//        template<typename T>
//        T operator &() const = delete;
//
//        operator z3::expr() = delete;
//        operator z3::expr& () = delete;
//        operator z3::expr& () const = delete;
//        operator const z3::expr() = delete;
//        operator const z3::expr& () = delete;
//        operator const z3::expr& () const = delete;
//    };
//
//    /*
//        GMP<UChar> ps = &x87_state.reg[0];  ok
//        UChar* p = &x87_state.reg[0];       err
//    */
//    template<typename ADDR, typename Type>
//    class GMP:private GM<ADDR, Type> {
//    public:
//        GMP(TR::MEM<ADDR>& obj, Vns const& base): GM<ADDR, Type>(obj, base)
//        {}
//
//        GMP(TR::MEM<ADDR>& obj) :GM<ADDR, Type>(obj)
//        {}
//
//        GMP(TR::MEM<ADDR>& obj, ADDR base) : GM<ADDR, Type>(obj, base)
//        {}
//
//        template<typename T>
//        GMP(TR::MEM<ADDR>& obj, T base) :GM<ADDR, Type>(obj, base)
//        {}
//
//        template<typename T>
//        GMP(GMP<ADDR, T> const &C) : GM<ADDR, Type>(C.obj(), ((GM<ADDR, T>&)C).m_base)
//        {}
//
//        /*template<typename T>
//        GMP(GM<T> const& C) : GM<Type>(C)
//        {}*/
//
//        TR::MEM<ADDR>& obj() const {
//            return static_cast<TR::MEM<ADDR>&>(m_obj);
//        }
//
//        /*template<typename T>
//        inline operator T () const {
//            return (T)m_base;
//        }*/
//
//
//        /*convert{*/
//        template <typename T>
//        inline operator GMP<ADDR, T>& () {
//            return static_cast<GMP<ADDR, T>&>(*this);
//        }
//        /*}convert*/
//
//        template<typename T>
//        inline void operator=(T const data) {
//            m_base = (ADDR)data;
//        }
//
//        inline void operator=(Vns const &data) {
//            m_base = data;
//        }
//
//
//        inline GM<ADDR, Type>& operator*() const {
//            return *(GM<ADDR, Type>*)this;
//        }
//
//
//        inline GM<ADDR, Type> operator [](UInt idx) {
//            return GM<ADDR, Type>(obj(), m_base + idx * (sizeof(Type)));
//        }
//
//
//
//    #define REG_OPERATOR(op)					\
//		    template<typename _dataType>		\
//		    inline GMP<ADDR, ype> operator op(_dataType data) const{\
//			    return GMP<ADDR, Type>(obj(), m_base + data * (sizeof(Type)));	\
//		    }
//
//        REG_OPERATOR(+);
//        REG_OPERATOR(-);
//        REG_OPERATOR(*);
//        REG_OPERATOR(/ );
//        REG_OPERATOR(>> );
//        REG_OPERATOR(<< );
//        REG_OPERATOR(| );
//        REG_OPERATOR(&);
//        REG_OPERATOR(== );
//
//    #undef REG_OPERATOR
//
//    private:
//        template<typename T>
//        inline GMP(GM<ADDR, T> const&) = delete;
//
//        /*Read{*/
//        template<typename T>
//        inline operator T () const = delete;
//        inline operator Vns () const = delete;
//        /*}Read*/
//
//        template<typename T>
//        T operator &() = delete;
//        template<typename T>
//        T operator &() const = delete;
//
//        operator z3::expr() = delete;
//        operator z3::expr& () = delete;
//        operator z3::expr& () const = delete;
//        operator const z3::expr() = delete;
//        operator const z3::expr& () = delete;
//        operator const z3::expr& () const = delete;
//    };
//
//
//    template<typename ADDR, typename Type>
//    class GR {
//        template <typename ADDR, typename T> friend class GRP;
//        friend class TRGL::VexGuestAMD64State;
//        friend class TRGL::VexGuestX86SegDescr;
//        friend class TRGL::VexGuestX86State;
//        TR::Register<REGISTER_LEN>& m_obj;
//        UInt ir_o;
//        GR(TR::Register<REGISTER_LEN>& obj, UInt iro) :
//            m_obj(obj),
//            ir_o(iro)
//        {}
//
//    public:
//        TR::Register<REGISTER_LEN>& obj() const {
//            return static_cast<TR::Register<REGISTER_LEN>&>(m_obj);
//        }
//
//    public:
//
//        /*Read{*/
//        template<typename T>
//        inline operator T () const {
//            return (T)(Type)obj().Iex_Get<(IRType)(sizeof(Type) << 3)>(ir_o);
//        }
//
//        inline operator Vns () const {
//            return obj().Iex_Get<(IRType)(sizeof(Type) << 3)>(ir_o);
//        }
//        /*}Read*/
//
//
//        /*Write{*/
//        template<typename T>
//        inline T operator=(T const data) {
//            obj().Ist_Put(ir_o, (Type)data);
//            return data;
//        }
//
//        void operator=(Vns const& data) {
//            if ((sizeof(Type) << 3) == data.bitn) {
//                obj().Ist_Put(ir_o, data);
//            }
//            else if ((sizeof(Type) << 3) > data.bitn) {
//                if (ISUNSIGNED_TYPE(Type)) {
//                    obj().Ist_Put(ir_o, data.zext(data.bitn - (sizeof(Type) << 3)));
//                }
//                else {
//                    obj().Ist_Put(ir_o, data.sext(data.bitn - (sizeof(Type) << 3)));
//                }
//            }
//            else {
//                obj().Ist_Put(ir_o, data.extract<(int)((sizeof(Type) << 3) - 1), 0>());
//            }
//        }
//        /*}Write*/
//
//        GRP<ADDR, Type>& operator &() const {
//            return *(GRP<ADDR, Type>*)this;;
//        }
//
//
//
//    #define REG_OPERATOR(op)					\
//		    template<typename _dataType>		\
//		    Vns operator op(_dataType data) const{\
//			    return operator Vns() op data;	\
//		    }
//
//        REG_OPERATOR(+);
//        REG_OPERATOR(-);
//        REG_OPERATOR(*);
//        REG_OPERATOR(/ );
//        REG_OPERATOR(>> );
//        REG_OPERATOR(<< );
//        REG_OPERATOR(| );
//        REG_OPERATOR(&);
//        REG_OPERATOR(== );
//
//    #undef REG_OPERATOR
//
//    private:
//        template<typename T>
//        inline GR(GR<ADDR, T> const &) = delete;
//
//        template<typename T>
//        T operator &() = delete;
//        template<typename T>
//        T operator &() const = delete;
//
//        operator z3::expr() = delete;
//        operator z3::expr& () = delete;
//        operator z3::expr& () const = delete;
//        operator const z3::expr() = delete;
//        operator const z3::expr& () = delete;
//        operator const z3::expr& () const = delete;
//    };
//
//
//    template<typename ADDR, typename Type>
//    class GRP :private GR<ADDR, Type> {
//    public:
//        GRP(TR::Register<REGISTER_LEN>& obj, UInt iro) : GR<ADDR, Type>(obj, iro)
//        {}
//
//        template<typename T>
//        GRP(GRP<ADDR, T> const& C) : GR<ADDR, Type>(C.obj(), ((GR<ADDR, T>&)C).ir_o)
//        {}
//
//        TR::Register<REGISTER_LEN>& obj() const {
//            return static_cast<TR::Register<REGISTER_LEN>&>(m_obj);
//        }
//
//        /*convert{*/
//        template <typename T>
//        inline operator GRP<ADDR, T>& () {
//            return static_cast<GRP<ADDR, T>&>(*this);
//        }
//        /*}convert*/
//
//        inline GR<ADDR, Type>& operator*() const {
//            return *(GR<ADDR, Type>*)this;
//        }
//
//
//        inline GR<ADDR, Type> operator [](UInt idx) {
//            return GR<ADDR, Type>(obj(), ir_o + idx * (sizeof(Type)));
//        }
//
//    #define REG_OPERATOR(op)					\
//		    template<typename _dataType>		\
//		    inline GR<ADDR, Type> operator op(_dataType offset) const{\
//			    return GR<ADDR, Type>(obj(), ir_o + offset * (sizeof(Type)));	\
//		    }
//
//        REG_OPERATOR(+);
//        REG_OPERATOR(-);
//        REG_OPERATOR(*);
//        REG_OPERATOR(/ );
//        REG_OPERATOR(>> );
//        REG_OPERATOR(<< );
//        REG_OPERATOR(| );
//        REG_OPERATOR(&);
//        REG_OPERATOR(== );
//
//    #undef REG_OPERATOR
//
//    private:
//        template<typename T>
//        inline GRP(GR<ADDR, T> const&) = delete;
//
//        template<typename T>
//        inline operator T () const = delete;
//
//        template<typename T>
//        T operator &() = delete;
//        template<typename T>
//        T operator &() const = delete;
//
//        operator z3::expr() = delete;
//        operator z3::expr& () = delete;
//        operator z3::expr& () const = delete;
//        operator const z3::expr() = delete;
//        operator const z3::expr& () = delete;
//        operator const z3::expr& () const = delete;
//    };
//
//
//    template<typename ADDR, typename Type, UInt shift = 0, UInt bits = (sizeof(Type) << 3)>
//    class GMW :private GM<ADDR, Type> {
//    public:
//        GMW(TR::MEM<ADDR>& obj, Vns const& base) :GM(obj, base)
//        {}
//
//        GMW(TR::MEM<ADDR>& obj) :GM(obj)
//        {}
//
//        GMW(TR::MEM<ADDR>& obj, ADDR base) :GM(obj, base)
//        {}
//
//        template<typename T>
//        GMW(TR::MEM<ADDR>& obj, T base) : GM(obj, base)
//        {}
//
//        operator Vns() const {
//            if (((sizeof(Type) << 3) == bits) && (shift == 0)) {
//                return ((GM<Type>*)this)->operator Vns();
//            }
//            if (ISUNSIGNED_TYPE(Type)) {
//                return ((GM<Type>*)this)->operator Vns().extract<(shift + bits - 1), shift>().zext((sizeof(Type) << 3) - bits);
//            }
//            else {
//                return ((GM<Type>*)this)->operator Vns().extract<(shift + bits - 1), shift>().sext((sizeof(Type) << 3) - bits);
//            }
//        }
//
//        template<typename T>
//        inline operator T () const {
//            return (T)(Type)this->operator Vns();
//        }
//    };
//
//};
//
//using namespace hp;
//
//
//
//#undef ISUNSIGNED_TYPE