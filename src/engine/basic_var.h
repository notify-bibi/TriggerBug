

#define TASSERT(v) std::enable_if_t<(v)> * = nullptr
#define fastMask(n) ((ULong)((((int)(n))<64)?((1ull << ((int)(n))) - 1):-1ll))
#define fastMaskReverse(N) (~fastMask(N))
#define ALIGN(Value,size) ((Value) & ~((size) - 1))

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


    template <class _Ty>
    constexpr bool is_sse_v = std::_Is_any_of_v < std::remove_cv_t<_Ty>, __m128d, __m128i, __m128, __m256d, __m256, __m256i>;

    template <class _Ty>
    struct is_my_struct : std::bool_constant<is_sse_v<_Ty>> {}; // determine whether _Ty is a class



    struct Signed128 {
        uint64_t m_v[2];
    };


    // 自定义你的有符号无符号类型
    template <class _Ty>
    struct is_my_signed : std::bool_constant <std::is_signed<_Ty>::value || std::_Is_any_of_v < std::remove_cv_t<_Ty>, 
        Signed128  /*,other type*/
    >>{};

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
        _CTX_ m_sk: 8;
        _CTX_ m_data_inuse : 8;

        _AST_ m_ast : 48;
        _AST_ m_bits : 16;


        template<typename _ty, int _tn, z3sk _tk> friend class ctype_val;
        template<bool _ts, int _tn, z3sk _tk> friend class symbolic;
        friend class tval;


        inline symbol(Z3_context ctx) : m_ctx((_CTX_)ctx), m_ast((_AST_)0) { }
        inline symbol(Z3_context ctx, int nbits) : m_ctx((_CTX_)ctx), m_ast((_AST_)0), m_bits(nbits) { }
        explicit inline symbol(Z3_context ctx, Z3_ast ast, z3sk sk) : m_ctx((_CTX_)ctx), m_sk(sk), m_ast((_AST_)ast) {
            dassert(ast);
            Z3_inc_ref(ctx, ast); 
        }

        explicit symbol(Z3_context ctx, uint64_t v, int nbits) : m_ctx((_CTX_)ctx), m_sk(Z3_BV_SORT) {
            Z3_sort zsort = Z3_mk_bv_sort(ctx, nbits);
            Z3_inc_ref((Z3_context)m_ctx, reinterpret_cast<Z3_ast>(zsort));
            m_ast = (_AST_)Z3_mk_unsigned_int64(ctx, v, zsort);
            Z3_inc_ref(ctx, (Z3_ast)m_ast);
            Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
        }

        explicit symbol(Z3_context ctx, int64_t v, int nbits) : m_ctx((_CTX_)ctx), m_sk(Z3_BV_SORT) {
            Z3_sort zsort = Z3_mk_bv_sort(ctx, nbits);
            Z3_inc_ref((Z3_context)m_ctx, reinterpret_cast<Z3_ast>(zsort));
            m_ast = (_AST_)Z3_mk_int64(ctx, v, zsort);
            Z3_inc_ref(ctx, (Z3_ast)m_ast);
            Z3_dec_ref(ctx, reinterpret_cast<Z3_ast>(zsort));
        }


        //explicit symbol(Z3_context ctx, uint64_t v, const sort& sort, z3sk sk) : m_ctx((_CTX_)ctx), m_sk(sk) {
        //    m_ast = (_AST_)Z3_mk_unsigned_int64(ctx, v, sort);
        //    Z3_inc_ref(ctx, (Z3_ast)m_ast);
        //}

        //explicit symbol(Z3_context ctx, int64_t v, const sort& sort, z3sk sk) : m_ctx((_CTX_)ctx), m_sk(sk) {
        //    m_ast = (_AST_)Z3_mk_int64(ctx, v, sort);
        //    Z3_inc_ref(ctx, (Z3_ast)m_ast);
        //}


        template<class _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(is_my_struct<_Ty>::value)>
        explicit inline symbol(Z3_context ctx, const _Ty& v, int nbits) : m_ctx((_CTX_)ctx), m_sk(Z3_BV_SORT) {
            m_ast = (_AST_)_mk_ast(ctx, (uint64_t*)&v, nbits);
            _simpify();
        }


        explicit symbol(Z3_context ctx, uint64_t* v, int nbit) : m_ctx((_CTX_)ctx), m_sk(Z3_BV_SORT) {
            m_ast = (_AST_)_mk_ast(ctx, v, nbit);
            _simpify();
        };

        template<class _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(is_my_struct<_Ty>::value) >
        explicit symbol(Z3_context ctx, const _Ty& v, const sort& fpa_sort, int nbits) : m_ctx((_CTX_)ctx), m_sk(Z3_FLOATING_POINT_SORT) {
            m_ast = (_AST_)_mk_ast(ctx, (uint64_t*)&v, nbits);
            Z3_ast fpa = Z3_mk_fpa_to_fp_bv(ctx, (Z3_ast)m_ast, fpa_sort);
            Z3_inc_ref(ctx, fpa);
            Z3_dec_ref(ctx, (Z3_ast)m_ast);
            m_ast = (_AST_)fpa;
            _simpify();
        }

        inline sort bool_sort() const { return sort((Z3_context)m_ctx, Z3_mk_bool_sort((Z3_context)m_ctx)); }
        inline sort bv_sort(unsigned ebits) const { return sort((Z3_context)m_ctx, Z3_mk_bv_sort((Z3_context)m_ctx, ebits)); }
        inline sort fpa_sort(unsigned ebits, unsigned sbits) const { return sort((Z3_context)m_ctx, Z3_mk_fpa_sort((Z3_context)m_ctx, ebits, sbits)); }
        template<int n> sort fpa_sort() const = delete;
        template<> inline sort fpa_sort<16>() const { return fpa_sort(5, 11); }
        template<> inline sort fpa_sort<32>() const { return fpa_sort(8, 24); }
        template<> inline sort fpa_sort<64>() const { return fpa_sort(11, 53); }
        template<> inline sort fpa_sort<128>() const { return fpa_sort(15, 113); }


        inline ~symbol() { if (m_ast) Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast); }


        template<class _Ty>
        explicit symbol(Z3_context ctx, _Ty v, struct mk_ast) : m_ctx((_CTX_)ctx) { static_assert(false, "error"); }

        template<class _Ty, TASSERT(sizeof(_Ty) <= 8)>
        symbol(Z3_context ctx, _Ty v, const sort& s, int nbits) : m_ctx((_CTX_)ctx) { static_assert(false, "ggggg"); }


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
            void _simpify() const {
                Z3_ast simp = Z3_simplify((Z3_context)m_ctx, (Z3_ast)m_ast);
                Z3_inc_ref((Z3_context)m_ctx, simp);
                Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                const_cast<symbol*>(this)->m_ast = (_AST_)simp;
            }
    };

    static sort fpRM(Z3_context m_ctx, IRRoundingMode md) {
        switch (md) {
        case Irrm_NEAREST: { return sort(m_ctx, Z3_mk_fpa_rne(m_ctx)); }
        case Irrm_PosINF: { return sort(m_ctx, Z3_mk_fpa_rtp(m_ctx)); }
        case Irrm_ZERO: { return sort(m_ctx, Z3_mk_fpa_rtz(m_ctx)); }
        case Irrm_NEAREST_TIE_AWAY_0: { return sort(m_ctx, Z3_mk_fpa_rna(m_ctx)); }
        case Irrm_NegINF: { return sort(m_ctx, Z3_mk_fpa_rtn(m_ctx)); }
        default: VPANIC("NOT SUPPPORT"); return *(sort*)(nullptr);
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
        using view_type = ite_type<std::is_integral<_Tty>::value || !std::is_floating_point<std::decay<_Tty>::type>::value, uint64_t,
                                  ite_type<std::is_same<std::decay<_Tty>::type, float>::value, float, double>::value_type
                                 >::value_type;

         
#pragma pack(push, 1)
        __declspec(align(8))
            view_type m_data[1 + (((_Tn - 1) >> 3) / sizeof(view_type))];
#pragma pack(pop)

        template<typename _t1, int _tn, z3sk _tk> friend class ctype_val;
        template<bool _ts, int _tn, z3sk _tk> friend class symbolic;
        friend class tval;
    public:
        template<int _tn = _Tn, TASSERT(_tn <= 64)>
        inline ctype_val(Z3_context ctx, _Tty data) :symbol(ctx) {
            static_assert(offsetof(ctype_val<_Tty>, m_data) == 0x10, "error");
            static_assert(_Tn > 0, "error");
            *(_Tty*)m_data = data;
        }
        // sse 
        template<int _tn = _Tn, TASSERT(_tn > 64)>
        inline ctype_val(Z3_context ctx,const _Tty& data) :symbol(ctx){
            static_assert(offsetof(ctype_val<_Tty>, m_data) == 0x10, "error");
            static_assert(_Tn > 0, "error");
            *(_Tty*)(m_data) = data;
        }

        // [ctype] v = ctype_val
        template<typename Ty, z3sk k = _Tk, TASSERT(k != Z3_BOOL_SORT)>
        inline operator Ty() const {
            return (Ty)(*(_Tty*)m_data); 
        }

        template<z3sk k = _Tk, TASSERT(k == Z3_BOOL_SORT)>
        inline operator bool() const { 
            return (bool)(((uint32_t*)m_data)[0] & 1);
        }

        // res
        template<typename _Ty1>
        inline ctype_val(const ctype_val<_Ty1>& b) :symbol((Z3_context)b.m_ctx) {
            *(_Tty*)m_data = *(_Ty1*)b.m_data;
        }

        template<typename _Ty>
        inline void operator=(const ctype_val<_Ty>& b) {
            ctype_val::~ctype_val();
            ctype_val::ctype_val(b);
        }
        template<int _tn = _Tn, TASSERT(_tn <= 64)>
        inline void operator=(_Tty b) {
            ctype_val::~ctype_val();
            m_ast = (_AST_)0;
            *(_Tty*)m_data = b;
        }
        // sse
        template<int _tn = _Tn, TASSERT(_tn > 64)>
        inline void operator=(const _Tty& b) {
            ctype_val::~ctype_val();
            m_ast = (_AST_)0;
            *(_Tty*)m_data = b;
        }

        inline operator Z3_context() const { return (Z3_context)m_ctx; }
        //Z3_BV_SORT
        template<z3sk k = _Tk, TASSERT(k == Z3_BV_SORT)>
        operator Z3_ast() const {
            if (!m_ast) 
                const_cast<ctype_val<_Tty>*>(this)->m_ast = (_AST_)_mk_ast((Z3_context)m_ctx, (uint64_t*)m_data, _Tn);
            return (Z3_ast)m_ast;
        }
        //bool
        template<z3sk k = _Tk, TASSERT(k == Z3_BOOL_SORT)>
        operator Z3_ast() const {
            //struct _Bst { uint8_t bit : 1; uint8_t oth : 7; };
            if (!m_ast) {
                const_cast<ctype_val*>(this)->m_ast = (_AST_)(((uint32_t*)m_data)[0]&1 ? Z3_mk_true((Z3_context)m_ctx) : Z3_mk_false((Z3_context)m_ctx));
                //const_cast<ctype_val*>(this)->m_ast = (_AST_)(((_Bst*)&m_data)->bit ? Z3_mk_true((Z3_context)m_ctx) : Z3_mk_false((Z3_context)m_ctx));
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
            }
            return (Z3_ast)m_ast;
        }

        //float
        template<z3sk k = _Tk, typename _t = _Tty, bool _f = std::is_same<std::decay<_t>::type, float>::value, TASSERT(k == Z3_FLOATING_POINT_SORT), TASSERT(_f)>
        operator Z3_ast() const {
            if (!m_ast) {
                const_cast<ctype_val*>(this)->m_ast = (_AST_)Z3_mk_fpa_numeral_float((Z3_context)m_ctx, *(_Tty*)m_data, fpa_sort<_Tn>());
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                dassert(m_ast);
            }
            return (Z3_ast)m_ast;
        }
        //double
        template<z3sk k = _Tk, typename _t = _Tty, bool _f = std::is_same<std::decay<_t>::type, double>::value, TASSERT(k == Z3_FLOATING_POINT_SORT && _f)>
        operator Z3_ast() const {
            if (!m_ast) {
                const_cast<ctype_val*>(this)->m_ast = (_AST_)Z3_mk_fpa_numeral_double((Z3_context)m_ctx, *(_Tty*)m_data, fpa_sort<_Tn>());
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                dassert(m_ast);
            }
            return (Z3_ast)m_ast;
        }

#define OPERATOR_DEFS(op) \
        template<typename _Ty1, int _tn, z3sk _Tk0 = _Tk, class _Rty = large_type<_Tty, _Ty1>::value_type, TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator op(const ctype_val<_Ty1, _tn>& b) const noexcept {\
            return ctype_val<_Rty, ite_val<int, (bool)(_Tn > _tn), _Tn, _tn>::value>((Z3_context)m_ctx, ((*(_Tty*)m_data) op (*(_Ty1*)b.m_data)));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator op(_Ty0 b) const noexcept {\
            return ctype_val<_Tty, _Tn>((Z3_context)m_ctx,(*(_Tty*)m_data op b));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        inline int operator op(_Ty0 b) const noexcept {\
            static_assert(false, "ctype_val<bool> "#op" num?");\
        }\

#if 1
        template<typename _Ty1, int _tn, z3sk _Tk0 = _Tk, class _Rty = large_type<_Tty, _Ty1>::value_type, TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator +(const ctype_val<_Ty1, _tn>& b) const noexcept {\
            return ctype_val<_Rty, ite_val<int, (bool)(_Tn > _tn), _Tn, _tn>::value >((Z3_context)m_ctx, ((*(_Tty*)m_data) + (*(_Ty1*)b.m_data)));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline auto operator +(_Ty0 b) const noexcept {\
            return ctype_val<_Tty, _Tn>((Z3_context)m_ctx,(*(_Tty*)m_data + b));\
        }\
        template<typename _Ty0, z3sk _Tk0 = _Tk, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        inline int operator +(_Ty0 b) const noexcept {\
            static_assert(false, "ctype_val<bool> + num?");\
        }\

#else
        OPERATOR_DEFS(+);
#endif
        OPERATOR_DEFS(-);
        OPERATOR_DEFS(*);
        OPERATOR_DEFS(/);
        OPERATOR_DEFS(%);

        OPERATOR_DEFS(| );
        OPERATOR_DEFS(&);
        OPERATOR_DEFS(^);

#undef OPERATOR_DEFS

#define OPERATOR_DEFS_BOOL(op) \
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 != Z3_BOOL_SORT)> \
        inline auto operator op(const ctype_val<_Ty1>& b) const noexcept { return ctype_val<bool>((Z3_context)m_ctx, (*(_Tty*)m_data) op *(_Ty1*)(b.m_data)); }\
        template<typename _Ty1, z3sk _Tk0 = _Tk,  TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)> \
        inline auto operator op(_Ty1 b) const noexcept { return ctype_val<bool>((Z3_context)m_ctx, (*(_Tty*)m_data) op b); }\
        template<typename _Ty1, z3sk _Tk0 = _Tk,  TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)> \
        inline int operator op(_Ty1 b) const noexcept { static_assert(false, "ctype_val(bool) "#op" num ?"); }\


        OPERATOR_DEFS_BOOL(> );
        OPERATOR_DEFS_BOOL(< );
        OPERATOR_DEFS_BOOL(>= );
        OPERATOR_DEFS_BOOL(<= );
        OPERATOR_DEFS_BOOL(== );
        OPERATOR_DEFS_BOOL(!= );

#define OPERATOR_DEFS_BOOL_OP(op)\
        template< z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BOOL_SORT)> \
        inline auto operator op(const ctype_val<bool>& b) const noexcept { return ctype_val<bool>((Z3_context)m_ctx, (*(bool*)m_data) op *(bool*)b.m_data); }\
        template< z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BOOL_SORT)> \
        inline auto operator op(bool b) const noexcept { return ctype_val<bool>((Z3_context)m_ctx, (*(bool*)m_data) op b); }\
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BOOL_SORT)> \
        inline int operator op(_Ty1 b) const noexcept { static_assert(false, "ctype_val(bool) "#op" num ?"); }

        OPERATOR_DEFS_BOOL_OP(&&);
        OPERATOR_DEFS_BOOL_OP(||);
        OPERATOR_DEFS_BOOL_OP(^);



#undef OPERATOR_DEFS_BOOL_OP
#undef OPERATOR_DEFS_BOOL

        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator <<(const ctype_val<_Ty1>& b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)((*(_Tty*)m_data) << (*(_Ty1*)b.m_data))); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator >>(const ctype_val<_Ty1>& b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)((*(_Tty*)m_data) >> (*(_Ty1*)b.m_data))); }


        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_integral<_Ty1>::value), TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator <<(_Ty1 b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)((*(_Tty*)m_data) << b)); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_integral<_Ty1>::value), TASSERT(_Tk0 == Z3_BV_SORT)>
        inline auto operator >>(_Ty1 b) const noexcept { return ctype_val<_Tty>((Z3_context)m_ctx, (_Tty)((*(_Tty*)m_data) >> b)); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_integral<_Ty1>::value), TASSERT(_Tk0 != Z3_BV_SORT)>
        inline int operator <<(_Ty1 b) const noexcept { static_assert(false, "ctype_val（not a Z3_BV_SORT） <<  num ?"); }
        template<typename _Ty1, z3sk _Tk0 = _Tk, TASSERT(std::is_integral<_Ty1>::value), TASSERT(_Tk0 != Z3_BV_SORT)>
        inline int operator >>(_Ty1 b) const noexcept { static_assert(false, "ctype_val（not a Z3_BV_SORT） >>  num ?"); }



        template<int __Tn = _Tn, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT), TASSERT(__Tn <= 64)>
        inline auto operator -() {
            return ctype_val((Z3_context)m_ctx, -(*(_Tty*)m_data));
        }
        template<int __Tn = _Tn, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(__Tn <= 64)>
        inline auto operator ~() {
            return ctype_val((Z3_context)m_ctx, ~(*(_Tty*)m_data));
        }

        template<int __Tn = _Tn, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(__Tn > 64 && __Tn<=128)>
        auto operator ~() {
            return ctype_val((Z3_context)m_ctx, _mm_xor_si128(*(__m128i*)m_data, _mm_set1_epi64x(-1)));
        }

        template<int __Tn = _Tn, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(__Tn > 128)>
        auto operator ~() {
            return ctype_val((Z3_context)m_ctx, _mm256_xor_si256(*(__m256i*)m_data, _mm256_set1_epi64x(-1)));
        }




        inline ~ctype_val() {}
        inline ctype_val translate(Z3_context target_ctx) const { return ctype_val(target_ctx, (*(_Tty*)m_data)); }


        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn <= 64), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char format[0x20];
            char buffer[0x40];
            snprintf(format, sizeof(format), "%cint%d_t< %%0%dllx >", is_my_signed<_Tty>::value ? 's' : 'u', _Tn, (1 + ((_Tn - 1) >> 3)) << 1);
            snprintf(buffer, sizeof(buffer), format, *(_Tty*)m_data);
            str.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 64 && _tn <= 128), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            snprintf(buffer, sizeof(buffer), "xmm%d< %016llx-%016llx >", _Tn, ((uint64_t*)m_data)[1], ((uint64_t*)m_data)[0]);
            str.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn > 128), TASSERT(_Tk0 == Z3_BV_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x60];
            snprintf(buffer, sizeof(buffer), "ymm%d< %016llx-%016llx-%016llx-%016llx >", _Tn, ((uint64_t*)m_data)[3], ((uint64_t*)m_data)[2], ((uint64_t*)m_data)[1], ((uint64_t*)m_data)[0]);
            str.assign(buffer);
            return str;
        }


        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn == 1), TASSERT(_Tk0 == Z3_BOOL_SORT)>
        std::string str() const {
            return ((*(int*)m_data) & 1) ? "bool<true>" : "bool<false>";
        }


        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn == 32), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            snprintf(buffer, sizeof(buffer), "float< %f >", *(float*)m_data);
            str.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(_tn == 64), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            snprintf(buffer, sizeof(buffer), "double< %lf >", *(double*)m_data);
            str.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(!(_tn == 64 || _tn == 32) && _tn <= 64), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char format[0x20];
            char buffer[0x40];
            snprintf(format, sizeof(format), "fpa%d< %%0%dllxh >", _Tn, (1 + ((_Tn - 1) >> 3)) << 1);
            snprintf(buffer, sizeof(buffer), format, *(_Tty*)m_data);
            str.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(!(_tn == 64 || _tn == 32) && _tn > 64 && _tn <= 128), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x40];
            snprintf(buffer, sizeof(buffer), "fpa%d< %016llx-%016llxh >", _Tn, ((uint64_t*)m_data)[1], ((uint64_t*)m_data)[0]);
            str.assign(buffer);
            return str;
        }

        template<int _tn = _Tn, z3sk _Tk0 = _Tk, TASSERT(!(_tn == 64 || _tn == 32) && _tn > 128), TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            std::string str;
            char buffer[0x60];
            snprintf(buffer, sizeof(buffer), "fpa%d< %016llx-%016llx-%016llx-%016llxh >", _Tn, ((uint64_t*)m_data)[3], ((uint64_t*)m_data)[2], ((uint64_t*)m_data)[1], ((uint64_t*)m_data)[0]);
            str.assign(buffer);
            return str;
        }

    };


#define OPERATOR_DEFS(op) \
        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline static auto operator op(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            return ctype_val<_Tty, _Tn>((Z3_context)b, a op (_Ty0)b);\
        }\
        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        static int operator op(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            static_assert(false, "num "#op" ctype_val<bool>?");\
        }

#if 1
        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)>\
        inline static auto operator +(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            return ctype_val<_Tty, _Tn>((Z3_context)b, a + (_Ty0)b);\
        }\
        template<typename _Ty0, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)>\
        static int operator +(_Ty0 a, const ctype_val<_Tty, _Tn, _Tk0>&b) {\
            static_assert(false, "num + ctype_val<bool>?");\
        }
#else
        OPERATOR_DEFS(+);
#endif

        OPERATOR_DEFS(-);
        OPERATOR_DEFS(*);
        OPERATOR_DEFS(/ );
        OPERATOR_DEFS(%);

        OPERATOR_DEFS(| );
        OPERATOR_DEFS(&);
        OPERATOR_DEFS(^);

#undef OPERATOR_DEFS


#define OPERATOR_DEFS_BOOL(op) \
template<typename _Ty1, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)> \
static inline auto operator op(_Ty1 a, const ctype_val<_Tty, _Tn, _Tk0>&b) noexcept { return ctype_val<bool>((Z3_context)b, a op ((_Tty)b) ); }\
template<typename _Ty1, typename _Tty, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BOOL_SORT)> \
static inline int operator op(_Ty1 a, const ctype_val<_Tty, _Tn, _Tk0>&b) noexcept { static_assert(false, "num "#op" ctype_val(bool) ?"); }


        OPERATOR_DEFS_BOOL(> );
        OPERATOR_DEFS_BOOL(< );
        OPERATOR_DEFS_BOOL(>= );
        OPERATOR_DEFS_BOOL(<= );
        OPERATOR_DEFS_BOOL(== );
        OPERATOR_DEFS_BOOL(!= );

#undef OPERATOR_DEFS_BOOL

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
        inline symbolic(Z3_context ctx, Z3_ast ast) :symbol(ctx, ast, _Tk) { }

        //bool(true/false)
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT)>
        inline symbolic(Z3_context ctx, bool b) : symbol(ctx, b ? Z3_mk_true(ctx) : Z3_mk_false(ctx),  Z3_BOOL_SORT) { };

        //same(same)
        template<typename _ty, int _tn, z3sk _tk, TASSERT(_tn == _Tn), TASSERT(_tk == _Tk)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b, _tk) { };

        //bool(nbv)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT), TASSERT(_tk == Z3_BV_SORT)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, ((uint32_t*)b.m_data)[0]&1 ? Z3_mk_true((Z3_context)b.m_ctx) : Z3_mk_false((Z3_context)b.m_ctx), Z3_BOOL_SORT) { };

        //nbv(bool)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(__Tn <= 64 ), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BOOL_SORT)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, Z3_mk_unsigned_int64((Z3_context)b.m_ctx, ((uint32_t*)b.m_data)[0] & 1, bv_sort(_Tn)), Z3_BV_SORT) {
            static_assert(_tn == 1, "err size");
        };

        ////bv (bv)  
        //template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(_tn == __Tn), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BV_SORT)>
        //inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b, Z3_BV_SORT) { };

        //bv (s bv)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(_tn < __Tn), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BV_SORT), TASSERT(is_my_signed<_ty>::value)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, Z3_mk_sign_ext((Z3_context)b.m_ctx, __Tn - _tn, (Z3_ast)b), Z3_BV_SORT) { };

        //bv (u bv)
        template<typename _ty, int _tn, z3sk _tk, z3sk __Tk = _Tk, int __Tn = _Tn, TASSERT(_tn < __Tn), TASSERT(__Tk == Z3_BV_SORT), TASSERT(_tk == Z3_BV_SORT), TASSERT(!is_my_signed<_ty>::value)>
        inline symbolic(const ctype_val<_ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, Z3_mk_zero_ext((Z3_context)b.m_ctx, __Tn - _tn, (Z3_ast)b), Z3_BV_SORT) { };

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
        template<typename _Ty, z3sk __Tk = _Tk, TASSERT(sizeof(_Ty) <= 8), TASSERT(std::is_integral<_Ty>::value), TASSERT(__Tk == Z3_BV_SORT) >
        inline symbolic(Z3_context ctx, _Ty v) : symbol(ctx, (ite_type<is_my_signed<_Ty>::value, int64_t, uint64_t>::value_type) v, _Tn) { };

        //bv(sse)
        template<typename _Ty, z3sk __Tk = _Tk, TASSERT((sizeof(_Ty) > 8)), TASSERT((sizeof(_Ty) << 3) == _Tn), TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic(Z3_context ctx, const _Ty& v) : symbol(ctx, v, _Tn) { };

        inline symbolic(const symbolic<_Tsigned, _Tn, _Tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b.m_ast, (z3sk)b.m_sk) { }
        
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
        template<bool _ts, int _tn, TASSERT(_tn < _Tn), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>                                      \
        inline auto operator op(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {                                                  \
            return *this op b.ext<_Tsigned, _Tn - _tn>();                                                                                       \
        }                                                                                                                                  \
        template<bool _ts, int _tn, TASSERT(_tn > _Tn), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>                                      \
        inline auto operator op(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {                                                  \
            return ext<_ts, _tn - _Tn>() op b;                                                                                        \
        }                                                                                                                                  \
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>                           \
        inline auto operator op(_Ty v) {                                                                                                   \
            return *this op symbolic<is_my_signed<_Ty>::value, sizeof(_Ty)<<3, Z3_BV_SORT>((Z3_context)m_ctx, v);                          \
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
            return *this + symbolic<is_my_signed<_Ty>::value, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, v);
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
        template<bool _ts, bool __Ts = _Tsigned,  z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(__Ts&&_ts)>                                \
        inline auto operator op(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {                                                          \
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, z3_sop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       \
        }                                                                                                                                          \
                                                                                                                                                   \
        template<bool _ts, bool __Ts = _Tsigned, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(!(__Ts&&_ts))>                              \
        inline auto operator op(const symbolic<_ts, _Tn, Z3_BV_SORT>& b) const noexcept {                                                          \
            return symbolic<_ts || _Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, z3_uop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));       \
        }                                                                                                                                          \




        TEMP_OPERATOR_BITWISHE_SIGN(/ , Z3_mk_bvsdiv, Z3_mk_bvudiv);
        TEMP_OPERATOR_BITWISHE_SIGN(% , Z3_mk_bvsrem, Z3_mk_bvurem);
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
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), TASSERT(!is_my_signed<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
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
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), TASSERT(!is_my_signed<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline auto operator >>(_Ty v) {
            return *this >> symbolic<false, Z3_BV_SORT>((Z3_context)m_ctx, v);
        };





        
        template<bool _Ts, z3sk _tk, z3sk __Tk = _Tk, TASSERT(_tk != Z3_FLOATING_POINT_SORT), TASSERT(__Tk != Z3_FLOATING_POINT_SORT)>
        inline auto operator ==(const symbolic<_Ts, _Tn, _tk>& b) const noexcept {
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, Z3_mk_eq((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
        }
        template<bool _Ts, z3sk _tk, z3sk __Tk = _Tk, TASSERT(_tk != Z3_FLOATING_POINT_SORT), TASSERT(__Tk != Z3_FLOATING_POINT_SORT)>
        inline auto operator !=(const symbolic<_Ts, _Tn, _tk>& b) const noexcept {
            symbolic<false, 1, Z3_BOOL_SORT> boolv((Z3_context)m_ctx, Z3_mk_eq((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, Z3_mk_not((Z3_context)m_ctx, (Z3_ast)boolv.m_ast));
        }

        template<bool _ts, int _tn, TASSERT(_tn < _Tn), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>               \
        inline auto operator ==(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {                           \
            return *this == b.ext<_ts, _Tn - _tn>();                                                                \
        }                                                                                                           \
        template<bool _ts, int _tn, TASSERT(_tn > _Tn), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>               \
        inline auto operator ==(const symbolic<_ts, _tn, Z3_BV_SORT>& b) const noexcept {                           \
            return ext<_Tsigned, _tn - _Tn>() == b;                                                                 \
        }                                                                                                           \
        template<class _Ty, TASSERT(std::is_integral<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>    \
        inline auto operator ==(_Ty v) {                                                                            \
            return *this == symbolic<is_my_signed<_Ty>::value, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, v);              \
        };


        //TEMP_OPERATOR_BITWISHE_NO_ALIGN(== ); 
        TEMP_OPERATOR_BITWISHE_NO_ALIGN(!= ); 


#define TEMP_OPERATOR_BOOL_OP(op, z3_sop)\
        template<bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT)>\
        inline auto operator op(const symbolic<_Ts, _Tn, Z3_BOOL_SORT>& b) const noexcept {\
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, z3_sop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }

        TEMP_OPERATOR_BOOL_OP(|| , Z3_mk_or);
        TEMP_OPERATOR_BOOL_OP(&& , Z3_mk_and);
        TEMP_OPERATOR_BOOL_OP(^ , Z3_mk_xor);


#undef TEMP_OPERATOR_BOOL_OP

#define TEMP_OPERATOR_BITWISHE_COMPARE(op, z3_sop, z3_uop)\
        template<bool __Ts = _Tsigned, bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(__Ts && _Ts)>\
        inline auto operator op(const symbolic<_Ts, _Tn, Z3_BV_SORT>& b) const noexcept {\
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, z3_sop((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }\
        template<bool __Ts = _Tsigned, bool _Ts, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(!(__Ts && _Ts))>\
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

        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        auto operator ~() {
            return symbolic<_Tsigned, _Tn, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_bvnot((Z3_context)m_ctx, (Z3_ast)m_ast));
        }


#undef TEMP_OPERATOR_BITWISHE
#undef TEMP_OPERATOR_BITWISHE_SIGN
#undef TEMP_OPERATOR_BITWISHE_COMPARE
#undef TEMP_OPERATOR_BITWISHE_NO_ALIGN

//-------------------------------fp------------------------------------

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


#define TEMP_OPERATOR_FP_COMPARE(op, z3_op)\
        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>\
        inline auto operator op(const symbolic<true, _Tn, Z3_FLOATING_POINT_SORT>& b) const noexcept {\
            return symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)m_ctx, z3_op((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)b.m_ast));\
        }\
        template<class _Ty, TASSERT(std::is_floating_point<_Ty>::value), z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>\
        inline auto operator op(_Ty v) {\
            return *this op symbolic<true, _Tn, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, v);\
        };\


        TEMP_OPERATOR_FP_COMPARE(== , Z3_mk_fpa_eq);
        TEMP_OPERATOR_FP_COMPARE(>, Z3_mk_fpa_gt);
        TEMP_OPERATOR_FP_COMPARE(<, Z3_mk_fpa_lt);
        TEMP_OPERATOR_FP_COMPARE(>=, Z3_mk_fpa_geq);
        TEMP_OPERATOR_FP_COMPARE(<=, Z3_mk_fpa_leq);

#undef TEMP_OPERATOR_FP_COMPARE
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
        template<unsigned ebits, unsigned sbits, bool _ts = _Tsigned, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(_ts)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> Integer2fpa(const sort& rm) const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_signed((Z3_context)m_ctx, rm, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };
        //unsigned int bv -> fp
        template<unsigned ebits, unsigned sbits, bool _ts = _Tsigned, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT), TASSERT(!_ts)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> Integer2fpa(const sort& rm) const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_unsigned((Z3_context)m_ctx, rm, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };
        //fp ->   signed int(bv)
        template<unsigned int bvsz, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<true , bvsz, Z3_BV_SORT> toInteger_sbv(const sort& rm) const {
            return symbolic<true, bvsz, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_sbv((Z3_context)m_ctx, rm, (Z3_ast)m_ast, bvsz));
        };
        //fp -> unsigned int (bv)
        template<unsigned int bvsz, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<false, bvsz, Z3_BV_SORT> toInteger_ubv(const sort& rm) const {
            return symbolic<false, bvsz, Z3_BV_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_ubv((Z3_context)m_ctx, rm, (Z3_ast)m_ast, bvsz));
        };
        //fp -> fp
        template<unsigned ebits, unsigned sbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT> fpa2fpa(const sort& rm) const {
            return symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>((Z3_context)m_ctx, Z3_mk_fpa_to_fp_float((Z3_context)m_ctx, rm, (Z3_ast)m_ast, fpa_sort(ebits, sbits)));
        };

//-----------------------------------bool------------------------------



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

        template<bool _ts, int _tn, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<_ts, _Tn + _tn, _Tk> concat(const sv::symbolic<_ts, _tn, _Tk>& lo) const {
            return sv::symbolic<_ts, _Tn + _tn, _Tk>((Z3_context)m_ctx, Z3_mk_concat((Z3_context)m_ctx, (Z3_ast)m_ast, (Z3_ast)lo.m_ast));
        }

        template<int hi, int lo, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<_Tsigned, hi - lo + 1, _Tk> extract() const {
            static_assert(lo >= 0 && hi < _Tn && lo <= hi, "????");
            return sv::symbolic<_Tsigned, hi - lo + 1, _Tk>((Z3_context)m_ctx, Z3_mk_extract((Z3_context)m_ctx, hi, lo, (Z3_ast)m_ast));
        }
        template<int nbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<_Tsigned, nbits, _Tk> extract(int hi, int lo) const {
            assert(hi - lo == nbits - 1);
            return sv::symbolic<_Tsigned, nbits, _Tk>((Z3_context)m_ctx, Z3_mk_extract((Z3_context)m_ctx, hi, lo, (Z3_ast)m_ast));
        }
        template<int nbits, z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        inline symbolic<_Tsigned, nbits, _Tk> extract(unsigned idx) const {
            assert(idx * nbits < _Tn);
            return sv::symbolic<_Tsigned, nbits, _Tk>((Z3_context)m_ctx, Z3_mk_extract((Z3_context)m_ctx, idx * nbits + (nbits - 1), idx * nbits, (Z3_ast)m_ast));
        }
    public:
        template<bool _s = _Tsigned, z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BV_SORT), TASSERT(_s)>
        std::string str() const {
            char buffer[0x40];
            snprintf(buffer, sizeof(buffer), "sbv%d< ", _Tn);
            return _str(buffer);
        }
        template<bool _s = _Tsigned, z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BV_SORT), TASSERT(!_s)>
        std::string str() const {
            char buffer[0x40];
            snprintf(buffer, sizeof(buffer), "ubv%d< ", _Tn);
            return _str(buffer);
        }

        template<z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_FLOATING_POINT_SORT)>
        std::string str() const {
            char buffer[0x40];
            snprintf(buffer, sizeof(buffer), "fpa%d< ", _Tn);
            return _str(buffer);
        }
        template<z3sk _Tk0 = _Tk, TASSERT(_Tk0 == Z3_BOOL_SORT)>
        std::string str() const {
            char buffer[0x40];
            snprintf(buffer, sizeof(buffer), "sbool< ");
            return _str(buffer);
        }
    private:
        std::string _str(char * buffer) const {
            std::string str, strContent;
            strContent.assign(buffer);
            str.append(strContent);
            strContent.assign(Z3_ast_to_string((Z3_context)m_ctx, (Z3_ast)m_ast));
            str.append(strContent);
            strContent.assign(" >");
            str.append(strContent);
            return str;
        }
    public:
        inline sort get_sort() const { return sort((Z3_context)m_ctx, Z3_get_sort((Z3_context)m_ctx, (Z3_ast)m_ast)); }
        inline Z3_sort_kind sort_kind() const { return Z3_get_sort_kind(m_ctx, get_sort()); }



        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BV_SORT)>
        tval simplify() const
        {
            symbolic simp((Z3_context)m_ctx, Z3_simplify((Z3_context)m_ctx, (Z3_ast)m_ast));
            if (Z3_get_ast_kind((Z3_context)m_ctx, simp) == Z3_NUMERAL_AST)
                return _numreal(simp);
            return simp;
        }


        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_BOOL_SORT)>
        tval simplify() const
        {
            symbolic simp((Z3_context)m_ctx, Z3_simplify((Z3_context)m_ctx, (Z3_ast)m_ast));
            Z3_func_decl f = Z3_get_app_decl((Z3_context)m_ctx, reinterpret_cast<Z3_app>((Z3_ast)simp));
            Z3_decl_kind dk = Z3_get_decl_kind((Z3_context)m_ctx, f);
            if (dk == Z3_OP_TRUE)
                return tval((Z3_context)m_ctx, true, (Z3_ast)simp, _Tk, 1);
            else if(dk == Z3_OP_FALSE)
                return tval((Z3_context)m_ctx, false, (Z3_ast)simp, _Tk, 1);
            return simp;
        }

        template<z3sk __Tk = _Tk, TASSERT(__Tk == Z3_FLOATING_POINT_SORT)>
        inline tval simplify() const
        {
            return tobv().simplify();
        }

    private:

        template<bool ts, int nbits>
        static tval _numreal(const symbolic<ts, nbits, Z3_BV_SORT>& simp) {
            Z3_context ctx = simp;
            if (_Tn <= 64) {
                uint64_t reval;
                Z3_get_numeral_uint64(ctx, simp, &reval);
                return tval(ctx, reval, nbits);
            }
            else {
                __m256i buff;
                Z3_get_numeral_bytes(ctx, simp, (ULong*)&buff);
                return tval(ctx, buff, nbits);
            }
        }
    };



#define SYM_OPERATOR_DEFS(op) \
template<typename _Ty0, bool _Ts, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BV_SORT), TASSERT(_Tn < (sizeof(_Ty0)<<3))>\
static auto operator op(_Ty0 a, const symbolic<_Ts, _Tn, _Tk0>&b) {\
    return symbolic<is_my_signed<_Ty0>::value, sizeof(_Ty0)<<3, Z3_BV_SORT>((Z3_context)b, a) op b;\
}\
template<typename _Ty0, bool _Ts, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BV_SORT), TASSERT(_Tn >= (sizeof(_Ty0)<<3))>\
static auto operator op(_Ty0 a, const symbolic<_Ts, _Tn, _Tk0>&b) {\
    return symbolic<is_my_signed<_Ty0>::value, _Tn, Z3_BV_SORT>((Z3_context)b, a) op b; \
}\
template<typename _Ty0, bool _Ts, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BV_SORT)>\
static int operator op(_Ty0 a, const symbolic<_Ts, _Tn, _Tk0>&b) {\
    static_assert(false, "num "#op" symbolic<bool>?");\
}

        template<typename _Ty0, bool _Ts, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BV_SORT), TASSERT(_Tn < (sizeof(_Ty0)<<3))>\
        static auto operator +(_Ty0 a, const symbolic<_Ts, _Tn, _Tk0>&b) {\
            return symbolic<is_my_signed<_Ty0>::value, sizeof(_Ty0)<<3, Z3_BV_SORT>((Z3_context)b, a) + b;\
        }\
        template<typename _Ty0, bool _Ts, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 == Z3_BV_SORT), TASSERT(_Tn >= (sizeof(_Ty0)<<3))>\
        static auto operator +(_Ty0 a, const symbolic<_Ts, _Tn, _Tk0>&b) {\
            return symbolic<is_my_signed<_Ty0>::value, _Tn, Z3_BV_SORT>((Z3_context)b, a) + b; \
        }\
        template<typename _Ty0, bool _Ts, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty0>::value), TASSERT(_Tk0 != Z3_BV_SORT)>\
        static int operator +(_Ty0 a, const symbolic<_Ts, _Tn, _Tk0>&b) {\
            static_assert(false, "num + symbolic<NOT A Z3_BV_SORT>?");\
        }

        SYM_OPERATOR_DEFS(-);
        SYM_OPERATOR_DEFS(*);
        SYM_OPERATOR_DEFS(/);
        SYM_OPERATOR_DEFS(%);

        SYM_OPERATOR_DEFS(| );
        SYM_OPERATOR_DEFS(&);
        SYM_OPERATOR_DEFS(^);



#define SYM_OPERATOR_DEFS_BOOL(op) \
template<typename _Ty1, bool _Ts, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 == Z3_BV_SORT)> \
static inline auto operator op(_Ty1 a, const symbolic<_Ts, _Tn, _Tk0>&b) noexcept { return symbolic<is_my_signed<_Ty1>, sizeof(_Ty0)<<3, Z3_BV_SORT>((Z3_context)b.m_ctx, a) op b; }\
template<typename _Ty1, bool _Ts, int _Tn, z3sk _Tk0, TASSERT(std::is_arithmetic<_Ty1>::value), TASSERT(_Tk0 != Z3_BOOL_SORT)> \
static inline int operator op(_Ty1 a, const symbolic<_Ts, _Tn, _Tk0>&b) noexcept { static_assert(false, "num "#op" symbolic<NOT A Z3_BV_SORT> ?"); }


        SYM_OPERATOR_DEFS_BOOL(> );
        SYM_OPERATOR_DEFS_BOOL(< );
        SYM_OPERATOR_DEFS_BOOL(>= );
        SYM_OPERATOR_DEFS_BOOL(<= );
        SYM_OPERATOR_DEFS_BOOL(== );
        SYM_OPERATOR_DEFS_BOOL(!= );

#undef SYM_OPERATOR_DEFS_BOOL

#undef SYM_OPERATOR_DEFS


};
    
namespace sv{
    class tval :protected symbol {
        uint64_t m_data[4];
    public:
        inline tval() : symbol((Z3_context)nullptr) {
            m_bits = -1;
            m_data_inuse = false;
        }
        inline tval(Z3_context ctx, Z3_ast s, z3sk sk, int bits) : symbol(ctx, s, sk) {
            m_bits = bits;
            m_data_inuse = false;
        }
    private:
        // translate a real bv
        inline tval(Z3_context target_ctx, const tval& b) : symbol(target_ctx) {
            dassert(b.m_data_inuse == true);
            m_bits = b.m_bits;
            m_data_inuse = true;
            if (b.m_bits <= 8) {
                m_data[0] = b.m_data[0];
            }
            else {
                *(__m256i*)m_data = _mm256_load_si256((__m256i*)b.m_data);
            }
        }
    public:
        inline tval(const tval& b) : symbol((Z3_context)b.m_ctx) {
            m_bits = b.m_bits;
            m_ast = b.m_ast;
            m_sk = b.m_sk;
            m_data_inuse = b.m_data_inuse;
            if (m_data_inuse) {
                if (m_bits <= 8) {
                    m_data[0] = b.m_data[0];
                }
                else {
                    *(__m256i*)m_data = _mm256_load_si256((__m256i*)b.m_data);
                }
            }
        }
        template<typename _Ty, std::enable_if_t<std::is_arithmetic<_Ty>::value> * = nullptr>
        inline tval(Z3_context ctx, _Ty data) :symbol(ctx) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            m_bits = sizeof(_Ty) << 3;
            m_data_inuse = true;
            *(_Ty*)m_data = data;
        }


        template<typename _Ty, std::enable_if_t<std::is_arithmetic<_Ty>::value> * = nullptr>
        inline tval(Z3_context ctx, _Ty data, Z3_ast ast, z3sk sk, int bits) :symbol(ctx, ast, sk) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            m_bits = bits;
            m_data_inuse = true;
            *(_Ty*)m_data = data;
        }


        template<typename _Ty, std::enable_if_t<std::is_arithmetic<_Ty>::value>* = nullptr>
        inline tval(Z3_context ctx, _Ty data, int bits) :symbol(ctx) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            m_bits = bits;
            m_data_inuse = true;
            *(_Ty*)m_data = data;
        }

        template<typename _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(is_my_struct<_Ty>::value)>
        inline tval(Z3_context ctx, const _Ty& data, int bits) :symbol(ctx) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            static_assert(sizeof(_Ty) <= 0x20, "error _TY");
            m_bits = bits;
            m_data_inuse = true;
            *(_Ty*)m_data = data;
        }

        template<typename _Ty, TASSERT(sizeof(_Ty) > 8), TASSERT(is_my_struct<_Ty>::value)>
        inline tval(Z3_context ctx, const _Ty& data, Z3_ast ast, z3sk sk, int bits) :symbol(ctx, ast, sk) {
            static_assert(offsetof(tval, m_data) == 0x10, "error");
            static_assert(sizeof(_Ty) <= 0x20, "error _TY");
            m_bits = bits;
            m_data_inuse = true;
            *(_Ty*)m_data = data;
        }

        template<typename _Ty, TASSERT(sizeof(_Ty) > 8)>
        inline tval(Z3_context ctx, const _Ty& data) :tval(ctx, data, (int)(sizeof(_Ty) << 3)) { }


        inline tval(Z3_context ctx, bool data) :symbol(ctx) {
            static_assert(offsetof(tval, m_data) == 0x10, "error"); 
            m_bits = 1;
            m_data_inuse = true;
            *(bool*)m_data = data;
        }

        template<typename _Ty, int _tn, z3sk _tk>
        inline tval(const ctype_val<_Ty, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx) {
            static_assert(_tn <= 0x100, "error _TY");
            static_assert((sizeof(_Ty) << 3) >= _tn, "error");
            m_bits = _tn;
            m_data_inuse = true;
            *(_Ty*)m_data = *(_Ty*)b.m_data;
        }

        template<bool _ts, int _tn, z3sk _tk>
        inline tval(const symbolic<_ts, _tn, _tk>& b) : symbol((Z3_context)b.m_ctx, (Z3_ast)b.m_ast, _tk) {
            m_bits = _tn;
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
        //-----------------------------------------------
        template<typename _Ty, int _tn, z3sk _tk>
        inline operator ctype_val<_Ty, _tn, _tk>&() const {
            dassert(_tn <= m_bits);
            dassert(m_data_inuse);
            return *reinterpret_cast<ctype_val<_Ty, _tn, _tk>*>(const_cast<tval*>(this));
        }

        template<bool _ts, int _tn>
        inline operator symbolic<_ts, _tn, Z3_BV_SORT>& () const {
            dassert(_tn == m_bits);
            mk_bv_ast();
            return *reinterpret_cast<symbolic<_ts, _tn, Z3_BV_SORT>*>(const_cast<tval*>(this));
        }

        inline operator symbolic<false, 1, Z3_BOOL_SORT>& () const {
            dassert(1 == m_bits);
            mk_bool_ast();
            return *reinterpret_cast<symbolic<false, 1, Z3_BOOL_SORT>*>(const_cast<tval*>(this));
        }

        template<bool s, int tn, TASSERT(!(tn == 16 || tn == 32 || tn == 64 || tn == 128))>
        inline operator symbolic<s, tn, Z3_FLOATING_POINT_SORT>& () const {
            static_assert(false, "use fpaRef<ebits, sbits>");
        };

        template<bool s, int tn, TASSERT(tn == 16)>
        inline operator symbolic<s, tn, Z3_FLOATING_POINT_SORT>& () const {
            return fpaRef<5, 11>();
        };

        template<bool s, int tn, TASSERT(tn == 32)>
        inline operator symbolic<s, tn, Z3_FLOATING_POINT_SORT>& () const {
            return fpaRef<8, 24>();
        };

        template<bool s, int tn, TASSERT(tn == 64)>
        inline operator symbolic<s, tn, Z3_FLOATING_POINT_SORT>& () const {
            return fpaRef<11, 53>();
        };

        template<bool s, int tn, TASSERT(tn == 128)>
        inline operator symbolic<s, tn, Z3_FLOATING_POINT_SORT>& () const {
            return fpaRef<15, 113>();
        };

        template<unsigned ebits, unsigned sbits>
        symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>& fpaRef() const {
            vassert(ebits + sbits == m_bits);
            mk_fpa_ast<ebits , sbits>();
            return *reinterpret_cast<symbolic<true, ebits + sbits, Z3_FLOATING_POINT_SORT>*>(const_cast<tval*>(this));
        }

        inline operator Z3_context() const { return (Z3_context)m_ctx; }
    private:

        static Z3_ast bool2bv(Z3_context ctx, Z3_ast ast) {
            Z3_inc_ref(ctx, ast);
            Z3_sort sort = Z3_mk_bv_sort(ctx, 1);
            Z3_inc_ref(ctx, (Z3_ast)sort);
            Z3_ast zero = Z3_mk_int(ctx, 0, sort);
            Z3_inc_ref(ctx, zero);
            Z3_ast one = Z3_mk_int(ctx, 1, sort);
            Z3_inc_ref(ctx, one);
            Z3_ast result = Z3_mk_ite(ctx, ast, one, zero);
            Z3_dec_ref(ctx, one);
            Z3_dec_ref(ctx, zero);
            Z3_dec_ref(ctx, ast);
            Z3_dec_ref(ctx, (Z3_ast)sort);
            return result;
        }

        Z3_ast mk_bv_ast() const {
            if (m_data_inuse && !m_ast) {
                const_cast<tval*>(this)->m_ast = (_AST_)_mk_ast((Z3_context)m_ctx, (uint64_t*)&m_data, m_bits);
                const_cast<tval*>(this)->m_sk = (_CTX_)Z3_BV_SORT;
                return (Z3_ast)m_ast;
            };
            if (m_sk == Z3_BV_SORT) {
                return (Z3_ast)m_ast;
            }
            if (m_sk == Z3_FLOATING_POINT_SORT) {
                Z3_ast bv = Z3_mk_fpa_to_ieee_bv((Z3_context)m_ctx, (Z3_ast)m_ast);
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)bv);
                Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                const_cast<tval*>(this)->m_ast = (_AST_)bv;
                const_cast<tval*>(this)->m_sk = (_CTX_)Z3_BV_SORT;
                return bv;
            }
            if (m_sk == Z3_BOOL_SORT) {
                Z3_ast bv = bool2bv((Z3_context)m_ctx, (Z3_ast)m_ast);
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)bv);
                Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                const_cast<tval*>(this)->m_ast = (_AST_)bv;
                const_cast<tval*>(this)->m_sk = (_CTX_)Z3_BV_SORT;
                return bv;
            }
            return (Z3_ast)-1;
            
        }
        inline Z3_ast mk_bool_ast() const {
            vassert(m_bits == 1);
            if (m_data_inuse && !m_ast) {
                const_cast<tval*>(this)->m_ast = (_AST_)(((*(int*)m_data) & 1) ? Z3_mk_true((Z3_context)m_ctx) : Z3_mk_false((Z3_context)m_ctx));
                const_cast<tval*>(this)->m_sk = (_CTX_)Z3_BOOL_SORT;
                return (Z3_ast)m_ast;
            }
            if (m_sk == Z3_BOOL_SORT) {
                return (Z3_ast)m_ast;
            }
            if (m_sk == Z3_BV_SORT) {
                Z3_sort sort = Z3_mk_bv_sort((Z3_context)m_ctx, 1);
                Z3_inc_ref((Z3_context)m_ctx, (Z3_ast)sort);
                Z3_ast one = Z3_mk_int((Z3_context)m_ctx, 1, sort);
                Z3_inc_ref((Z3_context)m_ctx, one);
                Z3_ast b = Z3_mk_eq((Z3_context)m_ctx, (Z3_ast)m_ast, one);
                Z3_inc_ref((Z3_context)m_ctx, b);
                Z3_dec_ref((Z3_context)m_ctx, one);
                Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)sort);
                Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                const_cast<tval*>(this)->m_ast = (_AST_)b;
                const_cast<tval*>(this)->m_sk = (_CTX_)Z3_BOOL_SORT;
                return b;
            }
            return (Z3_ast)-1;
        }
        template<unsigned ebits, unsigned sbits>
        inline Z3_ast mk_fpa_ast() const {
            static_assert(ebits > 0 && sbits > 0 && (sbits + ebits <= 256), "gg size");
            vassert(ebits + sbits == m_bits);
            if (m_data_inuse && !m_ast) {
                const_cast<tval*>(this)->m_ast = (_AST_)_mk_ast((Z3_context)m_ctx, (uint64_t*)&m_data, m_bits);
                sort s = sv::fpa_sort((Z3_context)m_ctx, ebits, sbits);
                Z3_ast fpa = Z3_mk_fpa_to_fp_bv((Z3_context)m_ctx, (Z3_ast)m_ast, s);
                Z3_inc_ref((Z3_context)m_ctx, fpa);
                Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                const_cast<tval*>(this)->m_ast = (_AST_)fpa;
                _simpify();
                const_cast<tval*>(this)->m_sk = (_CTX_)Z3_FLOATING_POINT_SORT;
                return fpa;
            }
            if (m_sk == Z3_FLOATING_POINT_SORT) {
                return (Z3_ast)m_ast;
            }
            if (m_sk == Z3_BV_SORT) {
                sort s = sv::fpa_sort((Z3_context)m_ctx, ebits, sbits);
                Z3_ast fpa = Z3_mk_fpa_to_fp_bv((Z3_context)m_ctx, (Z3_ast)m_ast, s);
                Z3_inc_ref((Z3_context)m_ctx, fpa);
                Z3_dec_ref((Z3_context)m_ctx, (Z3_ast)m_ast);
                const_cast<tval*>(this)->m_sk = (_CTX_)Z3_FLOATING_POINT_SORT;
                const_cast<tval*>(this)->m_ast = (_AST_)fpa;
                return fpa;
            }
            return (Z3_ast)-1;
        }


    public:
        //------------------------------------------------

        inline const uint64_t* cptr() const { return m_data; }

        inline bool symb() const { return m_data_inuse == false; }
        inline bool real() const { return m_data_inuse; }
        

        inline ~tval() {};
        inline tval translate(Z3_context target_ctx) const {
            if (m_data_inuse) {
                return tval(target_ctx, *this);
            }
            else {
                return tval(target_ctx, Z3_translate((Z3_context)m_ctx, (Z3_ast)m_ast, target_ctx), (z3sk)m_sk, (int)m_bits);
            }
        }

        inline uint32_t nbits() const { return m_bits; }
        

        public:

        std::string str() const {
            if (real()) {
                std::string str;
                char buff[0x80];

                if (m_bits <= 64) {
                    snprintf(buff, sizeof(buff), "tval %d( %d )", m_bits, (*(uint64_t*)m_data) & fastMask(m_bits)); goto ret;
                }
                if (m_bits <= 128) { 
                    snprintf(buff, sizeof(buff), "tval %d( %016llx %016llx )", m_bits, m_data[1], m_data[0]); goto ret;
                }
                if (m_bits <= 256) { 
                    snprintf(buff, sizeof(buff), "tval %d( %016llx %016llx %016llx %016llx )", m_bits, m_data[3], m_data[2], m_data[1], m_data[0]);  goto ret;
                }
                
            ret:
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


        tval extract(UInt hi, UInt lo) const {
            UShort size = hi - lo + 1;
            if (symb()) 
                return tval((Z3_context)m_ctx, Z3_mk_extract((Z3_context)m_ctx, hi, lo, (Z3_ast)m_ast), Z3_BV_SORT, size);
            
            if (lo < 64 && hi < 64) 
                return tval((Z3_context)m_ctx, m_data[0] >> lo, (hi - lo + 1));
            
            __m256i m32 = *(__m256i*)(&((char*)m_data)[lo >> 3]);
            if (lo & 7) {
                UChar _n = size >> 6;
                UChar _s = (64 - (lo & 7));
                for (int i = 0; i <= _n; i++) {
                    m32.m256i_u64[i] = (m32.m256i_u64[i] >> (lo & 7)) | (m32.m256i_u64[i + 1] << _s);
                }
            }
            return tval((Z3_context)m_ctx, m32, size);
        }


        tval concat(tval const& low) const {
            assert((low.m_bits + m_bits) <= 256);
            if (!low.m_bits) return *this;
            if (!m_bits) return low;
            if (real() && low.real()) {
                if (low.m_bits & 7) {
                    __m256i m32 = *(__m256i*)low.m_data;
                    auto base = ((low.m_bits - 1) >> 6);
                    m32.m256i_u64[base] &= fastMask(low.m_bits & 63);
                    auto shln = low.m_bits & 63;
                    auto shrn = (64 - shln);
                    m32.m256i_u64[base] |= m_data[0] << shln;
                    for (int i = 1; i <= ((m_bits - 1) >> 6); i++) {
                        m32.m256i_u64[base + i] = (m_data[i] << shln) | (m_data[i - 1] >> shrn);
                    }
                    return Vns((Z3_context)m_ctx, m32, low.m_bits + m_bits);
                }
                else {
                    __m256i re = *(__m256i*)low.m_data;
                    memcpy(&re.m256i_u8[(low.m_bits >> 3)], m_data, (this->m_bits) >> 3);
                    return Vns((Z3_context)m_ctx, re, low.m_bits + m_bits);
                }
            }
            else {
                return tval((Z3_context)m_ctx, Z3_mk_concat((Z3_context)m_ctx, (Z3_ast)m_ast, low.mk_bv_ast()), Z3_BV_SORT, low.m_bits + m_bits);
            }
        }

        
    };
};

using cBool = sv::ctype_val<bool>;
using cbool = sv::ctype_val<bool>;
using cUChar = sv::ctype_val<UChar>;
using cChar = sv::ctype_val<char>;
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
//sse
using cM128i = sv::ctype_val<__m128i>;
using cM128 = sv::ctype_val<__m128>;
using cM128d = sv::ctype_val<__m128d>;

using cM256i = sv::ctype_val<__m256i>;
using cM256  = sv::ctype_val<__m256>;
using cM256d = sv::ctype_val<__m256d>;

using tval = sv::tval;


using sbool = sv::symbolic<false, 1, Z3_BOOL_SORT>;
template<bool is_signed, int nbits> using bval = sv::symbolic<is_signed, nbits, Z3_BV_SORT>;
template<int nbits> using sbval = sv::symbolic< true, nbits, Z3_BV_SORT>;
template<int nbits> using ubval = sv::symbolic<false, nbits, Z3_BV_SORT>;
template<int nbits> using fpval = sv::symbolic< true, nbits, Z3_FLOATING_POINT_SORT>;
template<int nbits> using sfloat = sv::symbolic< true, 32, Z3_FLOATING_POINT_SORT>;
template<int nbits> using sdouble = sv::symbolic< true, 64, Z3_FLOATING_POINT_SORT>;

template<bool _ts, int _tn, sv::z3sk _tk>
inline sv::symbolic<_ts, _tn, _tk> ite( const sbool& _if, const sv::symbolic<_ts, _tn, _tk>& a, /*else*/  const sv::symbolic<_ts, _tn, _tk>& b) { return _if.ite(a, b); }
static inline sbool implies(sbool const& a, sbool const& b) { return a.implies(b); }
template<bool _ts, int _tn1, int _tn2, sv::z3sk _tk, TASSERT(_tk == Z3_BV_SORT)>
static inline sv::symbolic<_ts, _tn1 + _tn2, _tk> concat(const sv::symbolic<_ts, _tn1, _tk>& a, const sv::symbolic<_ts, _tn2, _tk>& b) { return a.concat(b); }
template<int hi, int lo, bool _ts, int _tn, sv::z3sk _tk, TASSERT(_tk == Z3_BV_SORT)>
inline auto extract(const sv::symbolic<_ts, _tn, _tk>& a) { return a.extract<hi, lo>(); }

template<bool _ts, int _tn, sv::z3sk _tk> 
static inline std::ostream& operator<<(std::ostream& out, sv::symbolic<_ts, _tn, _tk> const& n) { return out << n.str(); }
template<typename _Tty, int _tn, sv::z3sk _tk>
static inline std::ostream& operator<<(std::ostream& out, const sv::ctype_val<_Tty, _tn, _tk>& n) { return out << n.str(); }
static inline std::ostream& operator<<(std::ostream& out, sv::tval const& n) { return out << n.str(); }
static inline auto operator!(const sbool& b) {
    return sv::symbolic<false, 1, Z3_BOOL_SORT>((Z3_context)b, Z3_mk_not((Z3_context)b, (Z3_ast)b));
}

static inline tval concat(const tval& a, const tval& b) { return a.concat(b); }
