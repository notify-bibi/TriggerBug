#pragma once
#include "test.h"

using namespace TR;

#define TASSERT(v) std::enable_if_t<(v)> * = nullptr
namespace sv {
    template <class _Ty>
    struct type_constant {
        using value_type = std::remove_const<_Ty>::type;
    };

    template <class _Ty1, _Ty1 _Ty2>
    struct value_constant {
        static constexpr _Ty1 value = _Ty2;
    };

    template <class, class, bool>
    constexpr bool _choose_large_type = false;

    template <class _Ty1, class _Ty2>
    constexpr _Ty1 _choose_large_type<_Ty1, _Ty2, true> = (_Ty1)1;

    template <class _Ty1, class _Ty2>
    constexpr _Ty2 _choose_large_type<_Ty1, _Ty2, false> = (_Ty2)0;

    template <class _Ty1, class _Ty2>
    struct large_type : type_constant<decltype(_choose_large_type < _Ty1, _Ty2, sizeof(_Ty1) >= sizeof(_Ty2)>) > {};



    template <bool, class, class>
    constexpr auto _ite_type = false;//error

    template <class _Ty1, class _Ty2>
    constexpr auto _ite_type<true, _Ty1, _Ty2> = (_Ty1)1;

    template <class _Ty1, class _Ty2>
    constexpr auto _ite_type<false, _Ty1, _Ty2> = (_Ty2)1;

    template <bool _Tbool, class _Ty1, class _Ty2>
    struct ite_type : type_constant<decltype(_ite_type<_Tbool, _Ty1, _Ty2>)> {};

    template<class _Rty, bool _Tbool, _Rty _Ty1, _Rty _Ty2>
    struct _ite_val {
        static constexpr _Rty val = 0;
    };

    template<class _Rty, _Rty _Ty1, _Rty _Ty2>
    struct _ite_val<_Rty, true, _Ty1, _Ty2> {
        static constexpr _Rty val = _Ty1;
    };

    template<class _Rty, _Rty _Ty1, _Rty _Ty2>
    struct _ite_val<_Rty, false, _Ty1, _Ty2> {
        static constexpr _Rty val = _Ty2;
    };

    template <class _Rty, bool _Tbool, _Rty _Ty1, _Rty _Ty2>
    struct ite_val : value_constant<_Rty, _ite_val<_Rty, _Tbool, _Ty1, _Ty2>::val > {};


    template <class, class>
    constexpr auto _convert_type = false;

    template <class _Ty1, class _Ty2>
    constexpr auto _convert_type<_Ty1, _Ty2> = (_Ty1)0 + (_Ty1)0;

    template <class _Ty1, class _Ty2>
    struct convert : type_constant<decltype(_convert_type<_Ty1, _Ty2>)> {};





//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
    using z3sk = Z3_sort_kind;
    //   temp
    template<
        typename _Tty, int _Tn, z3sk _Tk 
    > class ctype_val;

    //   temp
    template<
        bool _is_signed, int _nbits, z3sk _sort_kind
    > class symbolic;

    ////   bool val
    //template<bool _is_signed, int _nbits>
    //class symbolic<_is_signed, _nbits, Z3_BOOL_SORT>;

    ////   signed Z3_BV_SORT
    //template<int _nbits >
    //class symbolic<true, _nbits, Z3_BV_SORT>;

    ////   UNsigned Z3_BV_SORT
    //template<int _nbits >
    //class symbolic<false, _nbits, Z3_BV_SORT>;

    ////   Z3_FLOATING_POINT_SORT
    //template<int _nbits >
    //class symbolic<false, _nbits, Z3_FLOATING_POINT_SORT>;

    //  VEX TEMP
    class tval;
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

};


namespace sv {

    class sort {
    public:
        Z3_context m_ctx;
        Z3_ast m_sort;
        inline sort(Z3_context ctx, Z3_ast sort) :m_ctx(ctx), m_sort(sort){ Z3_inc_ref(m_ctx, m_sort); }
        inline sort(Z3_context ctx, Z3_sort sort) : m_ctx(ctx), m_sort(reinterpret_cast<Z3_ast>(sort)) { Z3_inc_ref(m_ctx, m_sort); }
        inline operator Z3_ast () const { return m_sort; }
        inline operator Z3_sort () const { return reinterpret_cast<Z3_sort>(m_sort); }
        inline ~sort() { Z3_dec_ref(m_ctx, m_sort); }
    };




    __declspec(align(16))
        class symbol {
        using _CTX_ = size_t;
        using _AST_ = size_t;
        _CTX_ m_ctx : 48;
        _CTX_  : 8;
        _CTX_ m_data_inuse : 8;

        _AST_ m_ast : 48;
        _AST_ m_bits : 16;


        template<typename _ty, int _tn, z3sk _tk> friend class ctype_val;
        template<bool _ts, int _tn, z3sk _tk> friend class symbolic;
        friend class tval;


        inline symbol(Z3_context ctx) : m_ctx((_CTX_)ctx), m_ast((_AST_)0) { }
        inline symbol(Z3_context ctx, int nbits) : m_ctx((_CTX_)ctx), m_ast((_AST_)0), m_bits(nbits) { }
        inline symbol(Z3_context ctx, Z3_ast ast) : m_ctx((_CTX_)ctx), m_ast((_AST_)ast) {
            dassert(ast); 
            Z3_inc_ref(ctx, ast); 
        }
        inline symbol(Z3_context ctx, Z3_ast ast, int nbits) : m_ctx((_CTX_)ctx), m_ast((_AST_)ast), m_bits(nbits) { 
            dassert(ast);
            Z3_inc_ref(ctx, ast); 
        }


        template<class _Ty>
        symbol(Z3_context ctx, _Ty v, struct mk_ast) : m_ctx((_CTX_)ctx) {
            static_assert(std::is_arithmetic<_Ty>::value, "error");
            static_assert(sizeof(_Ty) <= 8, "error");
            Z3_sort zsort = Z3_mk_bv_sort(ctx, sizeof(_Ty) << 3);
            Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            m_ast = (_AST_)Z3_mk_unsigned_int64(ctx, *((uint64_t*)&v), zsort);
            Z3_inc_ref(ctx, (Z3_ast)m_ast);
            Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
        }

        template<class _Ty, TASSERT(sizeof(_Ty) <= 8), TASSERT(std::is_integral<_Ty>::value) >
        symbol(Z3_context ctx, _Ty v, int nbits) : m_ctx((_CTX_)ctx) {
            Z3_sort zsort = Z3_mk_bv_sort(ctx, nbits);
            Z3_inc_ref((Z3_context)m_ctx, reinterpret_cast<Z3_ast>(zsort));
            m_ast = (_AST_)Z3_mk_unsigned_int64(ctx, *((uint64_t*)&v), zsort);
            Z3_inc_ref(ctx, (Z3_ast)m_ast);
            Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
        }


        template<class _Ty, TASSERT(sizeof(_Ty) <= 8), TASSERT(std::is_arithmetic<_Ty>::value) >
        symbol(Z3_context ctx, _Ty v, const sort&s, int nbits) : m_ctx((_CTX_)ctx) {
            m_ast = (_AST_)Z3_mk_unsigned_int64(ctx, *((uint64_t*)&v), s);
            Z3_inc_ref(ctx, (Z3_ast)m_ast);
        }


        template<class _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(!std::is_class<_Ty>::value) >
       symbol(Z3_context ctx, const _Ty& v, const sort& s, int nbits) : m_ctx((_CTX_)ctx) {
            m_ast = (_AST_)_mk_ast(ctx, (uint64_t*)&v, nbits);
            Z3_ast fpa = Z3_mk_fpa_to_fp_bv(ctx, (Z3_ast)m_ast, s);
            Z3_inc_ref(ctx, fpa);
            Z3_dec_ref(ctx, (Z3_ast)m_ast);
            m_ast = (_AST_)fpa;
            _simpify();
        }

        template<class _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(!std::is_class<_Ty>::value)>
        inline symbol(Z3_context ctx, const _Ty& v, int nbits) : m_ctx((_CTX_)ctx) {
            m_ast = (_AST_)_mk_ast(ctx, (uint64_t*)&v, nbits);
            _simpify();
        }


        symbol(Z3_context ctx, uint64_t* v, int nbit) : m_ctx((_CTX_)ctx) {
            m_ast = (_AST_)_mk_ast(ctx, v, nbit);
            _simpify();
        };


        inline sort bool_sort() const { return sort((Z3_context)m_ctx, Z3_mk_bool_sort((Z3_context)m_ctx)); }
        inline sort bv_sort(unsigned ebits) const { return sort((Z3_context)m_ctx, Z3_mk_bv_sort((Z3_context)m_ctx, ebits)); }
        inline sort fpa_sort(unsigned ebits, unsigned sbits) const { return sort((Z3_context)m_ctx, Z3_mk_fpa_sort((Z3_context)m_ctx, ebits, sbits)); }
        template<int n> sort fpa_sort() const = delete;
        template<> inline sort fpa_sort<16>() const { return fpa_sort(5, 11); }
        template<> inline sort fpa_sort<32>() const { return fpa_sort(8, 24); }
        template<> inline sort fpa_sort<64>() const { return fpa_sort(11, 53); }
        template<> inline sort fpa_sort<128>() const { return fpa_sort(15, 113); }


        inline ~symbol() { if (m_ast) Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast); }





        static inline Z3_ast _mk_ast_(Z3_context ctx, uint64_t v, unsigned nb) {
            Z3_sort zsort = Z3_mk_bv_sort(ctx, nb);
            Z3_inc_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            Z3_ast r = Z3_mk_unsigned_int64(ctx, v, zsort);
            Z3_inc_ref(ctx, r);
            Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
            return r;
        }

        static inline Z3_ast _mk_ast(Z3_context ctx, const uint64_t* v, unsigned nbit) {
            Z3_ast r = _mk_ast_(ctx, v[(nbit - 1) >> 6], nbit - ALIGN(nbit - 1, 64));
            for (signed i = ((nbit - 1) >> 6) - 1; i >= 0; i--) {
                Z3_ast s = _mk_ast_(ctx, v[i], 64);
                Z3_ast nr = Z3_mk_concat(ctx, r, s);
                Z3_inc_ref(ctx, nr);
                Z3_dec_ref(ctx, s);
                Z3_dec_ref(ctx, r);
                r = nr;
            }
            return r;
        }
        private:
            void _simpify() {
                Z3_ast simp = Z3_simplify((Z3_context)m_ctx, (Z3_ast)m_ast);
                Z3_inc_ref((Z3_context)m_ctx, simp);
                Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                m_ast = (_AST_)simp;
            }
    };

    static sort fpRM(Z3_context m_ctx, IRRoundingMode md) {
        switch (md) {
        case Irrm_NEAREST: { return sort(m_ctx, Z3_mk_fpa_rne(m_ctx)); }
        case Irrm_PosINF: { return sort(m_ctx, Z3_mk_fpa_rtp(m_ctx)); }
        case Irrm_ZERO: { return sort(m_ctx, Z3_mk_fpa_rtz(m_ctx)); }
        case Irrm_NEAREST_TIE_AWAY_0: { return sort(m_ctx, Z3_mk_fpa_rna(m_ctx)); }
        case Irrm_NegINF: { return sort(m_ctx, Z3_mk_fpa_rtn(m_ctx)); }
        default: VPANIC("NOT SUPPPORT");
        }
    }

    inline sort bool_sort(Z3_context m_ctx)  { return sort((Z3_context)m_ctx, Z3_mk_bool_sort((Z3_context)m_ctx)); }
    inline sort bv_sort(Z3_context m_ctx, unsigned ebits)  { return sort((Z3_context)m_ctx, Z3_mk_bv_sort((Z3_context)m_ctx, ebits)); }
    inline sort fpa_sort(Z3_context m_ctx, unsigned ebits, unsigned sbits)  { return sort((Z3_context)m_ctx, Z3_mk_fpa_sort((Z3_context)m_ctx, ebits, sbits)); }
    template<int n> sort fpa_sort(Z3_context m_ctx) = delete;
    template<> inline sort fpa_sort<16>(Z3_context m_ctx)  { return fpa_sort(m_ctx, 5, 11); }
    template<> inline sort fpa_sort<32>(Z3_context m_ctx)  { return fpa_sort(m_ctx, 8, 24); }
    template<> inline sort fpa_sort<64>(Z3_context m_ctx)  { return fpa_sort(m_ctx, 11, 53); }
    template<> inline sort fpa_sort<128>(Z3_context m_ctx)  { return fpa_sort(m_ctx, 15, 113); }
}

namespace sv {
    template<
        typename _Tty,
        int _Tn = ite_val<int, std::is_same<std::decay<_Tty>::type, bool>::value, 1, (sizeof(_Tty) << 3)>::value,
        z3sk _Tk = ite_val<z3sk, std::is_same<std::decay<_Tty>::type, bool>::value, Z3_BOOL_SORT,/**/ ite_val<z3sk, std::is_floating_point<_Tty>::value, Z3_FLOATING_POINT_SORT, Z3_BV_SORT>::value /**/ >::value
    > class ctype_val : protected symbol {
        _Tty m_data;
        template<typename _t1, int _tn, z3sk _tk> friend class ctype_val;
        template<bool _ts, int _tn, z3sk _tk> friend class symbolic;
        friend class tval;
    public:
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value), TASSERT(sizeof(_Ty)<=8)>
        inline ctype_val(Z3_context ctx, _Ty data) :symbol(ctx), m_data(data) {
            static_assert(offsetof(ctype_val<_Tty>, m_data) == 0x10, "error");
            static_assert(_Tn > 0, "error");
        }
        // sse 
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value), TASSERT(sizeof(_Ty) > 8)>
        inline ctype_val(Z3_context ctx,const _Ty& data) :symbol(ctx){
            static_assert(offsetof(ctype_val<_Tty>, m_data) == 0x10, "error");
            static_assert(_Tn > 0, "error");
            *(_Ty*)(&m_data) = data;
        }

        // [ctype] v = ctype_val
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value)>
        inline operator _Ty() const { return (_Ty)m_data; }

        // res
        template<typename _Ty1>
        inline ctype_val(const ctype_val<_Ty1>& b) :symbol((Z3_context)b.m_ctx), m_data(b.m_data) {}

        template<typename _Ty>
        inline void operator=(const ctype_val<_Ty>& b) {
            ctype_val::~ctype_val();
            ctype_val::ctype_val(b);
        }
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value), TASSERT(sizeof(_Ty) <= 8) >
        inline void operator=(_Ty b) {
            ctype_val::~ctype_val();
            m_ast = (_AST_)0;
            m_data = b;
        }
        // sse
        template<typename _Ty, TASSERT(!std::is_class<_Ty>::value), TASSERT(!std::is_reference<_Ty>::value), TASSERT(sizeof(_Ty) > 8) >
        inline void operator=(const _Ty& b) {
            ctype_val::~ctype_val();
            m_ast = (_AST_)0;
            m_data = b;
        }

        inline operator Z3_context() const { return (Z3_context)m_ctx; }
        //Z3_BV_SORT
        template<z3sk k = _Tk, TASSERT(k == Z3_BV_SORT)>
        operator Z3_ast() const {
            if (!m_ast) 
                const_cast<ctype_val<_Tty>*>(this)->m_ast = (_AST_)_mk_ast((Z3_context)m_ctx, (uint64_t*)&m_data, _Tn);
            return (Z3_ast)m_ast;
        }
        //bool
        template<z3sk k = _Tk, TASSERT(k == Z3_BOOL_SORT)>
        operator Z3_ast() const {
            //struct _Bst { uint8_t bit : 1; uint8_t oth : 7; };
            if (!m_ast) {
                const_cast<ctype_val*>(this)->m_ast = (_AST_)(m_data ? Z3_mk_true((Z3_context)m_ctx) : Z3_mk_false((Z3_context)m_ctx));
                //const_cast<ctype_val*>(this)->m_ast = (_AST_)(((_Bst*)&m_data)->bit ? Z3_mk_true((Z3_context)m_ctx) : Z3_mk_false((Z3_context)m_ctx));
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
            }
            return (Z3_ast)m_ast;
        }

        //float
        template<z3sk k = _Tk, typename _t = _Tty, bool _f = std::is_same<std::decay<_t>::type, float>::value, TASSERT(k == Z3_FLOATING_POINT_SORT), TASSERT(_f)>
        operator Z3_ast() const {
            if (!m_ast) {
                const_cast<ctype_val*>(this)->m_ast = (_AST_)Z3_mk_fpa_numeral_float((Z3_context)m_ctx, m_data, fpa_sort<_Tn>());
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                dassert(m_ast);
            }
            return (Z3_ast)m_ast;
        }
        //double
        template<z3sk k = _Tk, typename _t = _Tty, bool _f = std::is_same<std::decay<_t>::type, double>::value, TASSERT(k == Z3_FLOATING_POINT_SORT && _f)>
        operator Z3_ast() const {
            if (!m_ast) {
                const_cast<ctype_val*>(this)->m_ast = (_AST_)Z3_mk_fpa_numeral_double((Z3_context)m_ctx, m_data, fpa_sort<_Tn>());
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                dassert(m_ast);
            }
            return (Z3_ast)m_ast;
        }

#define OPERATOR_DEFS(op) \
        template<typename _Ty1, z3sk _Tk0 = _Tk, class _Rty = large_type<_Tty, _Ty1>::value_type, TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator op(const ctype_val<_Ty1>& b) const noexcept {\
            return ctype_val<_Rty>((Z3_context)m_ctx, ( _Rty )((_Rty)m_data op(_Rty)b.m_data));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator op(_Ty0 b) const noexcept {\
            return ctype_val<_Tty, _Tn>((Z3_context)m_ctx, ( _Tty )((_Tty)m_data op(_Tty)b));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        inline int operator op(_Ty0 b) const noexcept {\
            static_assert(false, "ctype_val<bool> "#op" num?");\
        }\



        template<typename _Ty1, z3sk _Tk0 = _Tk, class _Rty = large_type<_Tty, _Ty1>::value_type, TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator +(const ctype_val<_Ty1>& b) const noexcept {\
            return ctype_val<_Rty>((Z3_context)m_ctx, ( _Rty )((_Rty)m_data +(_Rty)b.m_data));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator +(_Ty0 b) const noexcept {\
            return ctype_val<_Tty, _Tn>((Z3_context)m_ctx, ( _Tty )((_Tty)m_data +(_Tty)b));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        inline int operator +(_Ty0 b) const noexcept {\
            static_assert(false, "ctype_val<bool> + num?");\
        }\



        //OPERATOR_DEFS(+);
        OPERATOR_DEFS(-);
        OPERATOR_DEFS(*);
        OPERATOR_DEFS(/);
        OPERATOR_DEFS(%);

        OPERATOR_DEFS(| );
        OPERATOR_DEFS(&);
        OPERATOR_DEFS(^);

#undef OPERATOR_DEFS

#define OPERATOR_DEFS_bool(op) \
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 != Z3_BOOL_SORT)> \
        inline auto operator op(const ctype_val<_Ty1>& b) const noexcept { return ctype_val<bool>((Z3_context)m_ctx, m_data op b.m_data); }\
        template<typename _Ty1, z3sk _Tk0 = _Tk,  TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)> \
        inline auto operator op(_Ty1 b) const noexcept { return ctype_val<bool>((Z3_context)m_ctx, m_data op b); }\
        template<typename _Ty1, z3sk _Tk0 = _Tk,  TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)> \
        inline int operator op(_Ty1 b) const noexcept { static_assert(false, "ctype_val(bool) "#op" num ?"); }\


        OPERATOR_DEFS_bool(> );
        OPERATOR_DEFS_bool(< );
        OPERATOR_DEFS_bool(>= );
        OPERATOR_DEFS_bool(<= );
        OPERATOR_DEFS_bool(== );
        OPERATOR_DEFS_bool(!= );

#undef OPERATOR_DEFS_bool

        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator <<(const ctype_val<_Ty1>& b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)(m_data << b.m_data)); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator >>(const ctype_val<_Ty1>& b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)(m_data >> b.m_data)); }


        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator <<(_Ty1 b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)(m_data << b)); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator >>(_Ty1 b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)(m_data >> b)); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 != Z3_BV_SORT)>
        inline int operator <<(_Ty1 b) const noexcept { static_assert(false, "ctype_val£¨not a Z3_BV_SORT£© <<  num ?"); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BV_SORT)>
        inline int operator >>(_Ty1 b) const noexcept { static_assert(false, "ctype_val£¨not a Z3_BV_SORT£© >>  num ?"); }

        inline ~ctype_val() {}
        inline ctype_val translate(Z3_context target_ctx) const { return ctype_val(target_ctx, m_data); }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn <= 8), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %02x >", _Tn, m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 8 && _tn <= 16), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %04x >", _Tn, m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 16 && _tn <= 32), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %08x >", _Tn, m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 32 && _tn <= 64), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %016x >", _Tn, m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 64 && _tn <= 128), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %016x-%016x >", _Tn, ((uint64_t*)&m_data)[1], ((uint64_t*)&m_data)[0]);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 128), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " bv%d < %016x-%016x-%016x-%016x >", _Tn, ((uint64_t*)&m_data)[3], ((uint64_t*)&m_data)[2], ((uint64_t*)&m_data)[1], ((uint64_t*)&m_data)[0]);
            strContent.assign(buffer);
            return str;
        }


        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn == 1), TASSERT(_Tk0 == Z3_BOOL_SORT)>
        std::string str() const {
            std::string str;
            std::string strContent;
            char buffer[] = { "bool < g >" };
            buffer[7] = '0' + m_data;
            strContent.assign(buffer);
            return str;
        }


        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn == 32), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " float< %f >", *(float*)&m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn == 64), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " double< %lf >", *(double*)&m_data);
            strContent.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(!(_tn == 64 || _tn==32)), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " fpa%d< %08x >", m_bits, m_data);
            strContent.assign(buffer);
            return str;
        }
    };


#define OPERATOR_DEFS(op) \
template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT), TASSERT(_Tn < (sizeof(_Ty0)<<3))>\
static auto operator op(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
    return ctype_val<_Ty0>((Z3_context)b, a op (_Ty0)b);\
}\
template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT), TASSERT(_Tn > (sizeof(_Ty0)<<3))>\
static auto operator op(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
    return ctype_val<_Ty0>((Z3_context)b, a op (_Ty0)b);\
}\
template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
static int operator op(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
    static_assert(false, "num "#op" ctype_val<bool>?");\
}

        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT), TASSERT(_Tn < (sizeof(_Ty0)<<3))>\
        static auto operator +(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            return ctype_val<_Ty0>((Z3_context)b, a + (_Ty0)b);\
        }\
        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT), TASSERT(_Tn > (sizeof(_Ty0)<<3))>\
        static auto operator +(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            return ctype_val<_Ty0>((Z3_context)b, a + (_Ty0)b);\
        }\
        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        static int operator +(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            static_assert(false, "num + ctype_val<bool>?");\
        }\

        OPERATOR_DEFS(-);
        OPERATOR_DEFS(*);
        OPERATOR_DEFS(/ );
        OPERATOR_DEFS(%);

        OPERATOR_DEFS(| );
        OPERATOR_DEFS(&);
        OPERATOR_DEFS(^);

#undef OPERATOR_DEFS


#define OPERATOR_DEFS_bool(op) \
template<typename _Ty1, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)> \
static inline auto operator op(_Ty1 a, const ctype_val<_Tty, _Tn, _Tk0>&b) noexcept { return ctype_val<bool>((Z3_context)b.m_ctx, a op b.m_data ); }\
template<typename _Ty1, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)> \
static inline int operator op(_Ty1 a, const ctype_val<_Tty, _Tn, _Tk0>&b) noexcept { static_assert(false, "num "#op" ctype_val(bool) ?"); }


        OPERATOR_DEFS_bool(> );
        OPERATOR_DEFS_bool(< );
        OPERATOR_DEFS_bool(>= );
        OPERATOR_DEFS_bool(<= );
        OPERATOR_DEFS_bool(== );
        OPERATOR_DEFS_bool(!= );

#undef OPERATOR_DEFS_bool

};









namespace sv{


    // c type symbolic val
    template<
        bool _Tsigned,  //is signed value
        int  _Tn,       //nbits
        z3sk _Tk        // ze sort kind
    >
    class symbolic :protected symbol {
        template<bool _ts, int _tn, z3sk _tk> friend class symbolic;
        friend class tval;
    public:
        inline symbolic(Z3_context ctx, Z3_ast ast) :symbol(ctx, ast) { }

        //bool(true/false)
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT)>
        inline symbolic(Z3_context ctx, bool b) : symbol(ctx, b ? Z3_mk_true(ctx) : Z3_mk_false(ctx)) { };

        //same(same)
        template<typename _ty, int _tn, z3sk _tk, TASSERT(_tn == _Tn), TASSERT(_tk == _Tk)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b) { };

        //bool(nbv)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT), TASSERT(_tk == Z3_BV_SORT)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, b.m_data ? Z3_mk_true((Z3_context)b.m_ctx) : Z3_mk_false((Z3_context)b.m_ctx)) { };

        //nbv(bool)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(__Tn <= 64 ), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BOOL_SORT)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, Z3_mk_unsigned_int64((Z3_context)b.m_ctx, b.m_data ? 1 : 0, bv_sort(_Tn))) {
            static_assert(_tn == 1, "err size");
        };

        //bv (bv)  
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(_tn == __Tn), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BV_SORT)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b) { };

        //bv (s bv)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(_tn < __Tn), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BV_SORT), TASSERT(std::is_signed<_ty>::value)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, Z3_mk_sign_ext((Z3_context)b.m_ctx, __Tn - _tn, (Z3_ast)b)) { };

        //bv (u bv)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(_tn < __Tn), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BV_SORT), TASSERT(!std::is_signed<_ty>::value)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, Z3_mk_zero_ext((Z3_context)b.m_ctx, __Tn - _tn, (Z3_ast)b)) { };

        //float
        template<z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(__Tn == 32), TASSERT(__Tk == Z3_FLOATING_POINT_SORT) >
        inline symbolic(Z3_context ctx, float  v) : symbol(ctx, v, fpa_sort<32>(), _Tn) { };
        //double
        template<z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(__Tn == 64), TASSERT(__Tk == Z3_FLOATING_POINT_SORT) >
        inline symbolic(Z3_context ctx, double v) : symbol(ctx, v, fpa_sort<64>(), _Tn) { };
        //floating_point ( v bits[:])
        template<typename _Ty, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT((sizeof(_Ty) << 3) <= _Tn && sizeof(_Ty) < 8), TASSERT(std::is_integral<_Ty>::value), TASSERT(__Tk == Z3_FLOATING_POINT_SORT) >
        inline symbolic(Z3_context ctx, _Ty v, const sort& fp_sort) : symbol(ctx, v, fp_sort, _Tn) { };
        //floating_point large
        template<typename _Ty, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(sizeof(_Ty) > 8), TASSERT(__Tk == Z3_FLOATING_POINT_SORT) >
        inline symbolic(Z3_context ctx, const _Ty& v, const sort& fp_sort) : symbol(ctx, v, fp_sort, _Tn) { };


        //bv(integral)
        template<typename _Ty, z3sk __Tk = _Tk, TASSERT((sizeof(_Ty) << 3) <= _Tn), TASSERT(std::is_integral<_Ty>::value), TASSERT(__Tk == Z3_BV_SORT) >
        inline symbolic(Z3_context ctx, _Ty v) : symbol(ctx, (ite_type<std::is_signed<_Ty>::value, int64_t, uint64_t>::value_type) v, _Tn) { };

        //bv(sse)
        template<typename _Ty, z3sk __Tk = _Tk, TASSERT((sizeof(_Ty) > 8)), TASSERT((sizeof(_Ty) << 3) == _Tn), TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic(Z3_context ctx, const _Ty& v) : symbol(ctx, v, _Tn) { };

        inline symbolic(const symbolic& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b.m_ast) { }
        
        template<typename _Ty, int _tn, z3sk _tk>
        inline void operator =(const ctype_val<_Ty, _tn, _tk>& b) {
            this->symbolic::~symbolic();
            this->symbolic::symbolic(b);
        }
        template<bool _signed, int _tn, z3sk _tk>
        inline void operator =(const symbolic<_signed, _tn, _tk>& b) {
            this->symbolic::~symbolic();
            this->symbolic::symbolic(b);
        }

        inline operator Z3_context() const { return (Z3_context)m_ctx; }
        inline operator Z3_ast() const { return (Z3_ast)m_ast; }


        template<bool _Resig, int _extn, z3sk __Tk = _Tk, bool _Ts = _Tsigned, TASSERT(!_Ts), TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<_Resig, _Tn + _extn, _Tk> ext() const noexcept {
            static_assert(_extn > 0, "err size");
            return symbolic<_Resig, _Tn + _extn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_zero_ext((Z3_context)m_ctx, _extn, (Z3_ast)m_ast));
        }

        template<bool _Resig, int _extn, z3sk __Tk = _Tk, bool _Ts = _Tsigned, TASSERT(_Ts), TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<_Resig, _Tn + _extn, _Tk> ext() const noexcept {
            static_assert(_extn > 0, "err size");
            return symbolic<_Resig, _Tn + _extn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_sign_ext((Z3_context)m_ctx, _extn, (Z3_ast)m_ast));
        }












#define TEMP_OPERATOR_BITWISHE_NO_ALIGN(op)\
        template<bool _ts, int _tn, TASSERT(_tn < _Tn)>                                                                                    \
        inline auto operator op(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {                                                  \
            return *this op b.ext<_ts, _Tn - _tn>();                                                                                       \
        }                                                                                                                                  \
        template<bool _ts, int _tn, TASSERT(_tn > _Tn)>                                                                                    \
        inline auto operator op(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {                                                  \
            return ext<_Tsigned, _tn - _Tn>() op b;                                                                                        \
        }                                                                                                                                  \
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>                           \
        inline auto operator op(_Ty v) {                                                                                                   \
            return *this op symbolic<std::is_signed<_Ty>::value, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, v);                                   \
        };


#define TEMP_OPERATOR_BITWISHE(op, z3_op)\
        template<bool _ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>                                                                   \
        inline auto operator op(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {                                                  \
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, z3_op((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }                                                                                                                                 

        //add show 
        /*template<bool _ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator +(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvadd((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }
        template<bool _ts, int _tn, TASSERT(_tn < _Tn)>
        inline auto operator +(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {
            return *this + b.ext<_ts, _Tn - _tn>();
        }
        template<bool _ts, int _tn, TASSERT(_tn > _Tn)>
        inline auto operator +(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {
            return ext<_Tsigned, _tn - _Tn>() + b;
        }
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator +(_Ty v) {
            return *this + symbolic<std::is_signed<_Ty>::value, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, v);
        };*/



        TEMP_OPERATOR_BITWISHE(+, Z3_mk_bvadd);
        TEMP_OPERATOR_BITWISHE(-, Z3_mk_bvsub);
        TEMP_OPERATOR_BITWISHE(*, Z3_mk_bvmul);
        TEMP_OPERATOR_BITWISHE(| , Z3_mk_bvor);
        TEMP_OPERATOR_BITWISHE(&, Z3_mk_bvand);
        TEMP_OPERATOR_BITWISHE(^, Z3_mk_bvxor);

        TEMP_OPERATOR_BITWISHE_NO_ALIGN(+);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(-);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(*);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(|);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(&);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(^);



#define TEMP_OPERATOR_BITWISHE_SIGN(op, z3_sop, z3_uop)\
        template<bool _ts, bool __Ts = _Tsigned,  z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(__Ts)>                                     \
        inline auto operator op(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {                                                          \
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, z3_sop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       \
        }                                                                                                                                          \
                                                                                                                                                   \
        template<bool _ts, bool __Ts = _Tsigned, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(!__Ts)>                                     \
        inline auto operator op(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {                                                          \
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, z3_uop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       \
        }                                                                                                                                          \




        TEMP_OPERATOR_BITWISHE_SIGN(/ , Z3_mk_bvsdiv, Z3_mk_bvudiv);
        TEMP_OPERATOR_BITWISHE_SIGN(%, Z3_mk_bvsrem, Z3_mk_bvurem);
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(/ );
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(%);

        


        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator <<(const symbolic<false, _Tn, Z3_BV_SORT>& b) const noexcept {
            return symbolic<_Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvshl((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }

        template<int _tn, TASSERT(_tn < _Tn)>
        inline auto operator <<(const symbolic<false, _tn, Z3_BV_SORT>& b) const noexcept {
            return *this << b.ext<false, _Tn - _tn>();
        }
        template<int _tn, TASSERT(_tn > _Tn)>
        inline auto operator <<(const symbolic<false, _tn, Z3_BV_SORT>& b) const noexcept {
            return ext<_Tsigned, _tn - _Tn>() << b;
        }
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), TASSERT(!std::is_signed<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator <<(_Ty v) {
            return *this << symbolic<false, Z3_BV_SORT>((Z3_context)m_ctx, v);
        };





        template<bool __Ts = _Tsigned,  z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(__Ts)>                                     
        inline auto operator >>(const symbolic<false, _Tn, Z3_BV_SORT>& b) const noexcept {                                                          
            return symbolic<_Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvashr((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       
        }                                                                                                                                         
        template<bool __Ts = _Tsigned, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(!__Ts)>                                     
        inline auto operator >>(const symbolic<false, _Tn, Z3_BV_SORT>& b) const noexcept {
            return symbolic<_Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvlshr((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       
        }

        template<int _tn, TASSERT(_tn < _Tn)>
        inline auto operator >>(const symbolic<false, _tn, Z3_BV_SORT>& b) const noexcept {
            return *this >> b.ext<false, _Tn - _tn>();
        }
        template<int _tn, TASSERT(_tn > _Tn)>
        inline auto operator >>(const symbolic<false, _tn, Z3_BV_SORT>& b) const noexcept {
            return ext<_Tsigned, _tn - _Tn>() >> b;
        }
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), TASSERT(!std::is_signed<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator >>(_Ty v) {
            return *this >> symbolic<false, Z3_BV_SORT>((Z3_context)m_ctx, v);
        };







        template<bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator ==(const symbolic<_Ts, _Tn, Z3_BV_SORT>& b) const noexcept {
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, Z3_mk_eq((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }
        template<bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator !=(const symbolic<_Ts, _Tn, Z3_BV_SORT>& b) const noexcept {
            return ! symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, Z3_mk_eq((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(== ); 
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(!= ); 




#define TEMP_OPERATOR_BITWISHE_COMPARE(op, z3_sop, z3_uop)\
        template<bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(_Ts||_Tsigned)>\
        inline auto operator op(const symbolic<_Ts, _Tn, Z3_BV_SORT>& b) const noexcept {\
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, z3_sop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }\
        template<bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(!(_Ts||_Tsigned))>\
        inline auto operator op(const symbolic<_Ts, _Tn, Z3_BV_SORT>& b) const noexcept {\
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, z3_uop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }\
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(op)


        //ule
        TEMP_OPERATOR_BITWISHE_COMPARE(<= , Z3_mk_bvsle, Z3_mk_bvule);
        //ult
        TEMP_OPERATOR_BITWISHE_COMPARE(< , Z3_mk_bvslt, Z3_mk_bvult);
        //uge
        TEMP_OPERATOR_BITWISHE_COMPARE(>= , Z3_mk_bvsge, Z3_mk_bvuge);
        //ugt
        TEMP_OPERATOR_BITWISHE_COMPARE(> , Z3_mk_bvsgt, Z3_mk_bvugt);



        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        auto operator -() {
            return symbolic<_Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvneg((Z3_context)m_ctx, (Z3_ast)m_ast));
        }


#undef TEMP_OPERATOR_BITWISHE
#undef TEMP_OPERATOR_BITWISHE_SIGN
#undef TEMP_OPERATOR_BITWISHE_COMPARE
#undef TEMP_OPERATOR_BITWISHE_NO_ALIGN



#define TEMP_OPERATOR_FP(op, z3_op)\
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>\
        inline auto op(const sort& rm, const symbolic<true, _Tn, Z3_FLOATING_POINT_SORT>& b) const noexcept {\
            return symbolic<true, _Tn, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, z3_op((Z3_context)m_ctx, rm, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }\
        template<class _Ty, TASSERT(std::is_floating_point<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>\
        inline auto op(const sort& rm, _Ty v) {\
            return this->op(rm, symbolic<true, _Tn, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, v));\
        };\

        TEMP_OPERATOR_FP(add, Z3_mk_fpa_add);
        TEMP_OPERATOR_FP(sub, Z3_mk_fpa_sub);
        TEMP_OPERATOR_FP(mul, Z3_mk_fpa_mul);
        TEMP_OPERATOR_FP(div, Z3_mk_fpa_div);


#undef TEMP_OPERATOR_FP





        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        auto operator -() {
            return symbolic<_Tsigned, _Tn, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_neg((Z3_context)m_ctx, (Z3_ast)m_ast));
        }


        //bv -> ieee fpa
        template<unsigned ebits, unsigned sbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> tofpa() const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_bv((Z3_context)m_ctx, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };
        //fpa -> ieee bv
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<false, _Tn, Z3_BV_SORT> tobv() const {
            return symbolic<false, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_ieee_bv((Z3_context)m_ctx, (Z3_ast)m_ast));
        };
        //  signed int bv -> fp
        template<unsigned ebits, unsigned sbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> sInteger2fpa(const sort& rm) const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_signed((Z3_context)m_ctx, rm, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };
        //unsigned int bv -> fp
        template<unsigned ebits, unsigned sbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> uInteger2fpa(const sort& rm) const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_unsigned((Z3_context)m_ctx, rm, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };
        //fp ->   signed int(bv)
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<true , _Tn, Z3_BV_SORT> toInteger_sbv(const sort& rm) const {
            return symbolic<true, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_sbv((Z3_context)m_ctx, rm, (Z3_ast)m_ast));
        };
        //fp -> unsigned int (bv)
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<false, _Tn, Z3_BV_SORT> toIinteger_ubv(const sort& rm) const {
            return symbolic<false, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_ubv((Z3_context)m_ctx, rm, (Z3_ast)m_ast));
        };
        //fp -> fp
        template<unsigned ebits, unsigned sbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> fpa2fpa(const sort& rm) const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_float((Z3_context)m_ctx, rm, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };




        ~symbolic() {}



        inline symbolic translate(Z3_context target_ctx) const { return symbolic(target_ctx, Z3_translate((Z3_context)m_ctx, (Z3_ast)m_ast, target_ctx)); }

        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT)>
        symbolic<false, 1, Z3_BOOL_SORT> implies(const symbolic<false, 1, Z3_BOOL_SORT>& b) const {
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, Z3_mk_implies((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }
        //if
        template<bool _ts, int _tn, z3sk _tk, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT)>
        symbolic<_ts, _tn, _tk> ite(const symbolic<_ts, _tn, _tk>& a, const symbolic<_ts, _tn, _tk>& b) const {
            return symbolic<_ts, _tn, _tk>((Z3_context)m_ctx, Z3_mk_ite((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)a.m_ast, (Z3_ast)b.m_ast));
        }

        std::string str() const {
            std::string str;
            char buffer[0x40];
            std::string strContent;
            snprintf(buffer, sizeof(buffer), " BS%d < ", bitn);
            strContent.assign(buffer);
            str.append(strContent);
            strContent.assign(Z3_ast_to_string(m_ctx, m_ast));
            str.append(strContent);
            strContent.assign(" >");
            str.append(strContent);
            return str;
        }

    private:
    };
};
    
namespace sv{
    class tval :protected symbol {
        uint64_t m_data[4];
    public:
        inline tval(Z3_context ctx) :symbol(ctx, -1) {
            m_data_inuse = false;
        }
        inline tval() : symbol((Z3_context)nullptr, -1) {
            m_data_inuse = false;
        }
        inline tval(Z3_context ctx, Z3_ast s, int bits) : symbol(ctx, s, bits) {
            m_data_inuse = false;
        }
        // translate a real bv
        inline tval(Z3_context target_ctx, const tval& b) : symbol(target_ctx, b.m_bits) {
            assert(b.m_data_inuse == true);
            m_data_inuse = true;
            if (b.m_bits <= 8) {
                m_data[0] = b.m_data[0];
            }
            else {
                *(__m256i*)m_data = _mm256_load_si256((__m256i*)b.m_data);
            }
        }
        inline tval(const tval& b) : symbol((Z3_context)b.m_ctx, b.m_ast, b.m_bits) {
            m_data_inuse = b.m_data_inuse;
            if (m_data_inuse) {
                if (b.m_bits <= 8) {
                    m_data[0] = b.m_data[0];
                }
                else {
                    *(__m256i*)m_data = _mm256_load_si256((__m256i*)b.m_data);
                }
            }
        }
        template<typename _Ty, std::enable_if_t<std::is_arithmetic<_Ty>::value> * = nullptr>
        inline tval(Z3_context ctx, _Ty data) :symbol(ctx, (sizeof(_Ty) << 3)) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            *(_Ty*)m_data = data;
            m_data_inuse = true;
        }

        template<typename _Ty, std::enable_if_t<std::is_arithmetic<_Ty>::value>* = nullptr>
        inline tval(Z3_context ctx, _Ty data, int bits) :symbol(ctx, bits) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            *(_Ty*)m_data = data;
            m_data_inuse = true;
        }

        template<typename _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(!std::is_class<_Ty>::value)>
        inline tval(Z3_context ctx, const _Ty& data, int bits) :symbol(ctx, bits) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            static_assert(sizeof(_Ty) <= 0x20, "error _TY");
            *(_Ty*)m_data = data;
            m_data_inuse = true;
        }

        inline tval(Z3_context ctx, bool data) :symbol(ctx, 1) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            *(bool*)m_data = data;
            m_data_inuse = true;
        }

        template<typename _Ty, int _tn, z3sk _tk>
        inline tval(const ctype_val<_Ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, _tn) {
            static_assert(_tn <= 0x100, "error _TY");
            static_assert((sizeof(_Ty) << 3) >= _tn, "error");
            *(_Ty*)m_data = b.m_data;
            m_data_inuse = true;
        }

        template<bool _ts, int _tn, z3sk _tk>
        inline tval(const symbolic<_ts, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b.m_ast, _tn) {
            m_data_inuse = false;
        }

        inline tval(Z3_context ctx, const IRConst* con) :symbol(ctx)
        {
            m_data_inuse = true;
            switch (con->tag) {
            case Ico_U1:   m_bits = 1;  *(bool*)m_data = *(bool*)&(con->Ico.U1); return;
            case Ico_U8:   m_bits = 8;  *(uint8_t*)m_data= *(uint8_t*)&(con->Ico.U8); return;
            case Ico_U16:  m_bits = 16; *(uint16_t*)m_data = *(uint16_t*)&(con->Ico.U16); return;

            case Ico_U32:  
            case Ico_F32:  
            case Ico_F32i: m_bits = 32; *(uint32_t*)m_data = con->Ico.U32; return;

            case Ico_F64:  
            case Ico_F64i: 
            case Ico_U64:  m_bits = 64; *(uint64_t*)m_data = *(uint64_t*)&(con->Ico.U64); return;

            case Ico_V128: m_bits = 128; *(__m128i*)m_data = _mm_set1_epi16(con->Ico.V128); break;
            case Ico_V256: m_bits = 256; *(__m256i*)m_data = _mm256_set1_epi32(con->Ico.V256); break;
            default: VPANIC("tIRConst");
            }
        }


        template<typename _Ty, int _tn, z3sk _tk >
        inline void operator=(const ctype_val<_Ty, _tn, _tk>& b) {
            this->~tval();
            this->tval::tval(b);
        }

        template<bool _ts, int _tn, z3sk _tk>
        inline void operator=(const symbolic<_ts, _tn, _tk>& b) {
            this->~tval();
            this->tval::tval(b);
        }

        inline void operator=(const tval& b) {
            this->~tval();
            this->tval::tval(b);
        }

        template<typename _Ty, int _tn, z3sk _tk>
        operator ctype_val<_Ty, _tn, _tk>&() {
            return *reinterpret_cast<ctype_val<_Ty, _tn, _tk>*>(this);
        }

        template<bool _ts, int _tn, z3sk _tk>
        operator symbolic<_ts, _tn, _tk>& () {
            return *reinterpret_cast<symbolic<_ts, _tn, _tk>*>(this);
        }


        inline constexpr operator Z3_context() const { return (Z3_context)m_ctx; }

        inline bool symb() const { return m_data_inuse == false; }
        inline bool real() const { return m_data_inuse; }
        

        inline ~tval() {};
        inline tval translate(Z3_context target_ctx) const {
            if (m_data_inuse) {
                return tval(target_ctx, *this);
            }
            else {
                return tval(target_ctx, Z3_translate((Z3_context)m_ctx, (Z3_ast)m_ast, target_ctx), (int)m_bits);
            }
        }

        std::string str() const {
            if (real()) {
                std::string str;
                char buff[0x80];
                switch (m_bits) {
                case 1:   snprintf(buff, sizeof(buff), " val%d( %d )", m_bits, (*(bool*)m_data) & 1); break;
                case 8:   snprintf(buff, sizeof(buff), " val%d( %02x )", m_bits, *(uint8_t*)m_data); break;
                case 16:  snprintf(buff, sizeof(buff), " val%d( %04x )", m_bits, *(uint16_t*)m_data); break;
                case 32:  snprintf(buff, sizeof(buff), " val%d( %08x )", m_bits, *(uint32_t*)m_data); break;
                case 64:  snprintf(buff, sizeof(buff), " val%d( %016llx )", m_bits, *(uint64_t*)m_data); break;
                case 128: snprintf(buff, sizeof(buff), " val%d( %016llx %016llx )", m_bits, m_data[1], m_data[0]); break;
                case 256: snprintf(buff, sizeof(buff), " val%d( %016llx %016llx %016llx %016llx )", m_bits, m_data[3], m_data[2], m_data[1], m_data[0]); break;
                default:  snprintf(buff, sizeof(buff), " val%d( %016llx %016llx %016llx %016llx )", m_bits, m_data[3], m_data[2], m_data[1], m_data[0]); break;
                }
                str.assign(buff);
                return str;
            }
            else {
                std::string str;
                char buff[0x80];
#if 0
                std::string strContent;
                snprintf(buff, sizeof(buff), " BS%d < ", bitn);
                strContent.assign(buff);
                str.append(strContent);
                strContent.assign(Z3_ast_to_string(m_ctx, m_ast));
                str.append(strContent);
                strContent.assign(" >");
                str.append(strContent);
                return str;
#else
                snprintf(buff, sizeof(buff), " BVS %d < \\%p/ >  ", m_bits, m_ast);
                str.assign(buff);
                return str;
#endif
            }
        }
    };
};

using cBool = sv::ctype_val<bool>;
using cbool = sv::ctype_val<bool>;
using cUChar = sv::ctype_val<UChar>;
using cChar = sv::ctype_val<Char>;
using cUShort = sv::ctype_val<UShort>;
using cShort = sv::ctype_val<Short>;
using cint = sv::ctype_val<int>;
using cunsigned = sv::ctype_val<unsigned>;
using csigned = sv::ctype_val<signed>;
using cInt = sv::ctype_val<Int>;
using cUInt = sv::ctype_val<UInt>;
using cULong = sv::ctype_val<ULong>;
using cLong = sv::ctype_val<Long>;
using csize_t = sv::ctype_val<size_t>;
using cfloat = sv::ctype_val<float>;
using cdouble = sv::ctype_val<double>;
using tval = sv::tval;

using sbool = sv::symbolic<false, 1, Z3_BOOL_SORT>;
template<int nbits> using sbval = sv::symbolic< true, nbits, Z3_BV_SORT>;
template<int nbits> using ubval = sv::symbolic<false, nbits, Z3_BV_SORT>;
template<int nbits> using fpval = sv::symbolic< true, nbits, Z3_FLOATING_POINT_SORT>;
template<int nbits> using sfloat = sv::symbolic< true, 32, Z3_FLOATING_POINT_SORT>;
template<int nbits> using sdouble = sv::symbolic< true, 64, Z3_FLOATING_POINT_SORT>;

template<bool _ts, int _tn, sv::z3sk _tk>
inline sv::symbolic<_ts, _tn, _tk> ite( const sbool& _if, const sv::symbolic<_ts, _tn, _tk>& a, /*else*/  const sv::symbolic<_ts, _tn, _tk>& b) { return _if.ite(a, b); }
static inline sbool implies(sbool const& a, sbool const& b) { return a.implies(b); }

template<bool _ts, int _tn, sv::z3sk _tk> 
static inline std::ostream& operator<<(std::ostream& out, sv::symbolic<_ts, _tn, _tk> const& n) { return out << n.str(); }
template<class _Tty> 
static inline std::ostream& operator<<(std::ostream& out, sv::ctype_val<_Tty> const& n) { return out << n.str(); }
static inline std::ostream& operator<<(std::ostream& out, sv::tval const& n) { return out << n.str(); }


//using Vns = sv::tval;



void test1() {
    z3::context c;
    //sv::symbolic<false, 1, true> b5(c, false);

    //sv::tval bv(c);

    cUShort x1(c, 88);
    cunsigned x2(c, 8);
    sv::ctype_val<char, 1> u1(c, 0);
    sv::ctype_val<bool> b1(c, 0);
    sv::ctype_val<float> f1(c, 0.999);
    sv::ctype_val<double> d1(c, 0.999);

    c.fpa_val(9.0);

    


    Z3_ast ff = x1;
    ff = b1;
    ff = f1;
    ff = d1;
    auto fg = u1 + 1;
    fg = fg + 1;
    auto x3 = 8 + x1;

}

void test2() {
    z3::context c;


    sv::symbolic<true, 32, Z3_BV_SORT > d2(c, -5);
    sv::symbolic<false, 32, Z3_BV_SORT > d3(c, -5);
    sv::symbolic<false, 16, Z3_BV_SORT > d4(c, (UShort)-5);

    __m128i sd;
    sv::sort f65 = sv::fpa_sort(c, 10, 55);
    sv::symbolic<true, 65, Z3_FLOATING_POINT_SORT > d5(c, sd, f65);

    sv::sort rm = sv::fpRM(c, Irrm_NegINF);
    auto f1 = d5.fpa2fpa<5, 6>(rm);

    auto x1 = d2 + 8;
    auto x2 = d3 + 8;
    auto x3 = d2 + d3;
    auto x4 = d3 + d2;
    auto x5 = d4 + d2;
    auto x6 = d4 + d3;
    auto x7 = d2 + d4;
    auto x8 = d3 + d4;

}

int main() {
    test1();
    test2();
}



    //cbool b1(c, 8);
    //sv::ctype_val<const bool> b2(c, 8);
    //x1 = 8;

    //x1 = x1 + x2;
    //auto add1 = x1 + 88;
    //std::cout << z3::expr(c, add1) << std::endl;

    //bv = x1;
    //bv = b1;


    //sval<8> s8_0(c, 88);
    //auto add2 = s8_0 + 88;
    //add2 = 78 + s8_0;

    //std::cout << z3::expr(c, add2) << std::endl;

    //uval<8> u8_0(c, 8);
    //sbool b3(c, false);
    //sbool b4(c, true);


    //sval<32> s32_0(c, 88);

    //bv = s32_0;

    //__m256i m256i;
    //__m256 m256;
    //sval<256> s256_0(c, m256i);
    //sval<256> s256_1(c, m256);

    //std::cout << z3::expr(c, s256_0) << std::endl;


    //sval<32> s32_1(c, (char)-1);

    //uval<16> u16_0(c, 8ull);
    //sval<16> s16_0(c, 8);
    //uval<32> u32_0(c, 8);
    //uval<64> u64_0(c, 8);
    //sval<64> s64_0(c, 8);
    ////auto v1 = b3 || b4;


    //char charvalue = -2;
    //sval<32> s32_2(c, charvalue);
    //uval<32> u32_2(c, charvalue);

    //std::cout << z3::expr(c, s32_1) << std::endl;
    //std::cout << z3::expr(c, u32_0) << std::endl;
    //std::cout << z3::expr(c, s32_2) << std::endl;
    //std::cout << z3::expr(c, u32_2) << std::endl;

    //auto v2 = u32_0 + s16_0;
    //std::cout << z3::expr(c, s16_0) << std::endl;
    //std::cout << z3::expr(c, v2) << std::endl;
    //auto df0 = u16_0 + s32_0;


    //auto dd = ite(u32_0 != s16_0, s32_1>>6, s32_0);

    //std::cout << z3::expr(c, dd) << std::endl;
    //auto df1 = g4 + g2;
    //auto df2 = g33 + g2;



//
//State_Tag success_ret(Kernel* _s) {
//    vex_printf("success_ret  ??????????\n\n%d");
//    return (State_Tag)0x999;
//
//    s->solv.push();
//    auto ecx = s->regs.Iex_Get<Ity_I32>(12);
//    auto edi = s->regs.Iex_Get<Ity_I32>(36);
//
//    for (int i = 0; i < 44; i++) {
//        auto al = s->mem.Iex_Load<Ity_I8>(ecx + i);
//        auto bl = s->mem.Iex_Load<Ity_I8>(edi + i);
//        s->solv.add(al == bl);
//    }
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("sat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    return Death;
//}
//
//
//State_Tag success_ret2(State* s) {
//
//    s->solv.push();
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("sat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    exit(1);
//    return Death;
//}
//
//




State_Tag success_ret3(State<Addr64>* s) {
    s->solv.push();
    UChar bf[] = { 0xEC, 0x29, 0xE3, 0x41, 0xE1, 0xF7, 0xAA, 0x1D, 0x29, 0xED, 0x29, 0x99, 0x39, 0xF3, 0xB7, 0xA9, 0xE7, 0xAC, 0x2B, 0xB7, 0xAB, 0x40, 0x9F, 0xA9, 0x31, 0x35, 0x2C, 0x29, 0xEF, 0xA8, 0x3D, 0x4B, 0xB0, 0xE9, 0xE1, 0x68, 0x7B, 0x41 };

    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RDI);
    for (int i = 0; i < 38; i++) {
        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
        s->solv.add(e == (UChar)bf[i]);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == z3::sat) {
        vex_printf("issat");
        auto m = s->solv.get_model();
        std::cout << m << std::endl;
        exit(0);
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    
    s->solv.pop();
    return Death;
}
//
//
//State_Tag success_ret33(State* s) {
//    s->solv.push();
//    UChar bf[] = { 133, 67, 104, 133, 245, 38, 60, 61, 39, 245, 51, 104, 62, 60, 118, 38, 245, 118, 165, 245, 19, 165, 61, 245, 62, 165, 45, 61, 245, 7, 60, 118, 29, 60, 15, 0, 133, 169 };
//
//    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rax);
//    for (int i = 0; i < 38; i++) {
//        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
//        s->solv.add(e == (UChar)bf[i]);
//    }
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("issat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//        exit(0);
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    return Death;
//}
//
//
//State_Tag whil(State* s) {
//    return (State_Tag)0x233;
//}
//
//State_Tag pp(State* s) {
//    auto al = s->regs.Iex_Get<Ity_I32>(AMD64_IR_OFFSET::eax);
//    std::cout << Z3_ast_to_string(al, al) << std::endl;
//    s->regs.Ist_Put(AMD64_IR_OFFSET::rax, 38ull);
//    s->hook_pass(5);
//    return (State_Tag)Running;
//}
//
//State_Tag Dea(State* s) {
//    return (State_Tag)Death;
//}



#include "engine/guest_layout_helper.h"

Vns flag_limit(Vns& flag) {
    char flags_char[] = "@_-{}1:() ^";
    Vns re = Vns(flag, flags_char[0]) == flag;
    for (int i = 1; i < sizeof(flags_char); i++) {
        re = re || (Vns(flag, flags_char[i]) == flag);
    }
    auto ao1 = flag >= 'a' && flag <= 'z';
    auto ao2 = flag >= 'A' && flag <= 'Z';
    auto ao3 = flag >= '0' && flag <= '9';
    return re || ao1 || ao2 || ao3;
}



State_Tag test_ir_dirty_hook(State<Addr32>& state) {
    UInt esp = 0x8000 - 532;
    PWOW64_CONTEXT ContextRecord = (PWOW64_CONTEXT)(esp - sizeof(WOW64_CONTEXT));
    PEXCEPTION_RECORD32 ExceptionRecord = (PEXCEPTION_RECORD32)(esp - sizeof(WOW64_CONTEXT) - sizeof(EXCEPTION_RECORD32));

    if ((UInt)state.vex_stack_get(1) != (Addr32)(ULong)ContextRecord) return Death;
    if ((UInt)state.vex_stack_get(2) != EXCEPTION_BREAKPOINT) return Death;
    if ((UInt)state.vex_stack_get(22 + offsetof(WOW64_CONTEXT, Esp) / 4) != 0x8000) return Death;
    return Exit;
}

bool test_ir_dirty() {
    ctx32 v(VexArchX86, "");
    v.set_system(windows);
    v.param().set("ntdll_KiUserExceptionDispatcher", 0x2000);

    SP::win32 state(v, 0, True);
    state.setFlag(CF_traceJmp);
    state.setFlag(CF_ppStmts);
    state.mem.map(0x1000, 0x2000);
    state.mem.map(0x5000, 0x5000);
    state.hook_add(0x2000, test_ir_dirty_hook);
    state.mem.Ist_Store(0x1000, 0xcc);

    state.regs.Ist_Put(X86_IR_OFFSET::ESP, 0x8000);
    state.regs.Ist_Put(X86_IR_OFFSET::EIP, 0x1000);
    state.regs.Ist_Put(X86_IR_OFFSET::CC_OP, 0x0);


    state.start(0x1000);

    return state.status() == Exit;
}

bool creakme();
bool asong();


bool test_cmpress() {
    ctx64 v(VexArchAMD64, "");
    SP::linux64 state(v, 0, True);

    state.mem.map(0x602000, 0x2000);
    state.mem.map(0x5000, 0x5000);

    for (int i = 0; i < 4; i++) {
        SP::linux64* s = (SP::linux64*)(state.ForkState(20));
        Vns f1 = s->m_ctx.bv_const("a1", 8);
        Vns f2 = s->m_ctx.bv_const("a2", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->mem.Ist_Store(0x602080, 1000 + i);
        s->mem.Ist_Store(0x602088, 1000 + i);
        if (i == 3)
            s->set_status(Death);
    }
    std::cout << state << std::endl;
    for (int i = 4; i < 5; i++) {
        SP::linux64* s = (SP::linux64*)(state.ForkState(32));
        Vns f1 = s->m_ctx.bv_const("aj", 8);
        Vns f2 = s->m_ctx.bv_const("ak", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->set_status((State_Tag)88);
    }

    std::cout << state << std::endl;
    UInt i = 0;
    for (auto s : state.branch) {
        i += 1;
        if (i <= 3) { continue; }
        SP::linux64* s2 = (SP::linux64*)(s->ForkState(20));
        s->set_status(Fork);
        Vns f = s2->m_ctx.bv_const("b", 8);
        s2->solv.add_assert(f > i);
        s2->mem.Ist_Store(0x602080, 100 + i);
        s2->mem.Ist_Store(0x602081, 100ull + i + (1ull << 63));
        if (i <= 4)
            continue;
        s2->m_InvokStack.push(787, 87);
    }


    std::cout << state << std::endl;


    cmpr::Context64 c = state.cmprContext(20, NewState);
    c.add_avoid(Death);
    c.add_avoid((State_Tag)88);

    state.compress(c);
    std::cout << state << std::endl;
    return true;
}


bool test_dirty_cmpress() {
    ctx64 v(VexArchAMD64, PROJECT_DIR"PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.xml");
    SP::linux64 state(v, 0, True);


    UChar bf[] = { 0xD9 ,0x74 ,0x24 ,0xE2 };
    for (int i = 0; i < sizeof(bf); i++) {
        state.mem.Ist_Store(state.get_cpu_ip() + i, bf[i]);
    }
    Vns f = state.m_ctx.bv_const("b", 64);
    state.solv.add_assert(f != 0);
    state.regs.Ist_Put(AMD64_IR_OFFSET::FPTAG, f);
    state.start();

    std::cout << state << std::endl;
    return true;
}
//int main() {
//    //testz3();
//    //IR_TEST(test_ir_dirty);
//    IR_TEST(creakme);
//    IR_TEST(asong);
//    IR_TEST(test_cmpress);
//
//}

//int main() {
//    {
//        flag_max_count = 38+6;
//        flag_count = 0;
//
//        StatePrinter<StateAMD64> state(INIFILENAME, 0, True);
//        state.hook_add(0x400CC0, success_ret3);
//        StateAnalyzer gv(state);
//        gv.Run();
//    };
//    return 0;
//}

//
//int main() {
//    flag_max_count = 1;
//    flag_count = 0;
//
//    StatePrinter<StateX86> state(INIFILENAME, 0, True);
//
//    context& c = state;
//
//    for (int i = 0; i < 32; i++) {
//        auto flag = state.get_int_const(8);
//        auto ao1 = flag >= 'a' && flag <= 'f';
//        auto ao3 = flag >= '0' && flag <= '9';
//        state.mem.Ist_Store(i + 0x0019F554, flag);
//        state.add_assert(ao1 || ao3, 1);
//        if (i == 31) {
//            _VexGuestX86State reg(state);
//            state.mem.Ist_Store(reg.guest_EBP-0x24, flag);
//        }
//    }
//
//
//    state.hook_add(0x4050B0, Dea);
//    state.hook_add(0x4050D0, success_ret2);
//
//    State::pushState(state);
//    State::pool->wait();
//
//    return 0;
//}


//

