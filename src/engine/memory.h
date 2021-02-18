#pragma once
/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    Memory.class:
Abstract:
    Address mapping technique;
    Copy-on-Write;
    Fork technology;
    符号地址解析
    符号地址爆破
    符号地址存取;
Author:
    WXC 2019-10-28
Revision History:
--*/


//#ifndef MEMORY_DEFS_H
//#define MEMORY_DEFS_H

#include "engine/engine.h"
#include "engine/basic_var.hpp"
#include "engine/register.h"
#include "engine/mem_map.h"





#ifdef _DEBUG
#define NEED_VERIFY 
#define TRACE_AM
#endif


class PAGE_DATA;
class PAGE_PADDING;
namespace TR {

    template <class _Ty1, class = void>
    struct store_value_type {
        using type = _Ty1;
    };


    template <class _Ty>
    struct is_large : std::bool_constant<sv::is_sse_v<_Ty> || std::is_class_v<_Ty>> {};

    template <class _Ty>
    constexpr bool is_large_v = is_large<_Ty>::value;


    template <class _Ty>
    struct is_large_ctype : std::bool_constant< (sv::is_sse_v<_Ty> || (sizeof(_Ty) > 8)) && !std::is_class_v<_Ty> > {};

    template <class _Ty>
    constexpr bool is_large_ctype_v = is_large_ctype<_Ty>::value;


    template <class _Ty1>
    struct store_value_type<_Ty1, class std::enable_if<is_large_v<_Ty1>> > {
        using type = typename std::add_lvalue_reference_t<std::add_const_t<_Ty1>>;
    };

    template <class _Ty1>
    using store_value_type_t = typename store_value_type<_Ty1>::type;


    class MBase;
    class Mem;
};

constexpr double ANALYZER_TIMEOUT = 0.4;

#define LINETOSTR(A) #A
#define CONCATSTR(A, B) " ACCESS MEM ERR UNMAPPED; " A " AT Line: " LINETOSTR(B)

//客户机内存访问检查
#define MEM_ACCESS_ASSERT_R(CODE, HWordESS) if UNLIKELY(!(CODE)) throw Expt::GuestMemReadErr(CONCATSTR(__FILE__, __LINE__), HWordESS);
#define MEM_ACCESS_ASSERT_W(CODE, HWordESS) if UNLIKELY(!(CODE)) throw Expt::GuestMemWriteErr(CONCATSTR(__FILE__, __LINE__), HWordESS);


class PAGE {
    enum PageTy
    {
        mem_INVALID,
        mem_PADDING,
        mem_CODE,
        mem_DATA
    };

    Int m_user;
    std::atomic_int m_ref_cound;
    PageTy m_mem_ty = mem_INVALID;
    friend class PAGE_DATA;
    friend class PAGE_PADDING;
    friend class TR::MBase;

    inline PAGE(Int u, PageTy mem_ty) : m_user(u), m_ref_cound(1), m_mem_ty(mem_ty){};
    inline void set_user(Int u) {  m_user = u; };
public:
    inline ~PAGE() noexcept(false) { vassert(m_ref_cound == 0); }
    inline Int  get_user() const { return m_user; };
    inline bool is_code() { return m_mem_ty == mem_CODE; };
    inline bool is_data() { return m_mem_ty == mem_DATA || m_mem_ty == mem_CODE; };
    inline bool is_padding() { return m_mem_ty == mem_PADDING; };
    inline void set_code_flag() { m_mem_ty = mem_CODE; };

    inline void inc_used_ref() {
        vassert(m_ref_cound); m_ref_cound++;
    }

    inline int get_used_ref() const { return m_ref_cound; }

    inline bool dec_used_ref() {
        vassert(m_ref_cound); return (bool)(--m_ref_cound);
    }

    inline void check_ref_cound(int n) { vassert(m_ref_cound == n); }

    virtual PAGE_DATA* get_write_page(int user, PAGE* pt[1]/*in&out*/, z3::vcontext& ctx) { return nullptr; }
};

class TR::mem_unit : public TR::Register<0x1000> {
    Int m_user;
    using page_class = TR::Register<0x1000>;
    friend class PAGE_DATA;
    friend class PAGE_PADDING;

    inline mem_unit(Int u, z3::vcontext& ctx) : page_class(ctx), m_user(u){ }
    inline mem_unit(Int u, z3::vcontext& ctx, UChar init_value) : page_class(ctx), m_user(u) { memset(m_bytes, init_value, sizeof(m_bytes)); }
    //翻译转换父register
    inline mem_unit(Int u, TR::mem_unit& father_page, z3::vcontext& ctx) : page_class((page_class&)father_page, ctx), m_user(u) { }
public:
    template<bool sign, int nbits, sv::z3sk sk>
    inline sv::rsval<sign, nbits, sk> load(Int target_user, UInt idx, z3::vcontext& target_ctx) {
        if UNLIKELY(m_user == target_user) {
            return page_class::get<sign, nbits, sk>(idx);
        }
        else {
            return page_class::get<sign, nbits, sk>(idx, target_ctx);
        }
    }

    inline sv::tval Iex_Get(Int target_user, UInt offset, UInt nbytes, z3::vcontext& target_ctx) {
        if UNLIKELY(m_user == target_user) {
            return page_class::Iex_Get(offset, nbytes);
        }
        else {
            return page_class::Iex_Get(offset, nbytes, target_ctx);
        }
    }
    const UChar* get_bytes(UInt offst) { return &page_class::m_bytes[offst]; }
};


class PAGE_DATA : public PAGE {
    friend class TR::MBase;
    friend class TR::Mem;
    friend class PAGE_PADDING;
    TR::mem_unit m_unit;
    inline PAGE_DATA(Int u,
        z3::vcontext& ctx
    ) : PAGE(u, mem_DATA), m_unit(u, ctx) { }


    inline PAGE_DATA(Int u,
        z3::vcontext& ctx, UChar init_value
    ) : PAGE(u, mem_DATA), m_unit(u, ctx, init_value) { }

    // translate
    inline PAGE_DATA(Int u,
        PAGE_DATA& father, z3::vcontext& ctx
    ) : PAGE(u, mem_DATA), m_unit(u, father.get_unit(), ctx) { }

    TR::mem_unit& get_unit() { return m_unit; }
    const UChar* get_bytes(UInt offst) { return m_unit.get_bytes(offst); }

    inline bool is_code() = delete;
    inline bool is_data() = delete;
    inline bool is_padding() = delete;
    virtual PAGE_DATA* get_write_page(int user, PAGE* pt[1]/*in&out*/, z3::vcontext& ctx) override;
};


// 该页是填充区
class PAGE_PADDING : public PAGE {
    friend class PAGE_DATA;
    friend class TR::MBase;
    friend class TR::Mem;

    UChar m_padding_value = 0xcc;
    __m256i m_padding;

    inline PAGE_PADDING(Int u, UChar pad_value) : PAGE(u, mem_PADDING), m_padding_value(pad_value) { m_padding = _mm256_set1_epi8(m_padding_value); }
public:
    template<bool sign, int nbits, sv::z3sk sk>
    inline sv::rsval<sign, nbits, sk> load(UInt idx, Z3_context target_ctx) {
        return sv::rsval<sign, nbits, sk>(target_ctx, (UChar*)&m_padding);
    }
    inline void set_padding_value(UChar v) { m_padding_value = v;  m_padding = _mm256_set1_epi8(v); }
    inline UChar get_padding_value() const { return m_padding_value; }
    static PAGE_DATA* convert_to_data(PAGE* pt[1]/*in&out*/, z3::vcontext& ctx);

    inline bool is_code() = delete;
    inline bool is_data() = delete;
    inline bool is_padding() = delete;
    virtual PAGE_DATA* get_write_page(int user, PAGE* pt[1]/*in&out*/, z3::vcontext& ctx) override;
};

#define pto_data(p)      ((PAGE_DATA*)  (p))
#define pto_padding(p)  ((PAGE_PADDING*)(p))




class DMem;

namespace TR {
    typedef enum {
        enough,
        swap_state,
        next_page
    }Insn_linear_flag;

    typedef struct __declspec(align(16)) {
        unsigned char swap[48];
        Insn_linear_flag flag;
        UInt the_rest_n;
        const UChar* guest_addr_in_page;
        Addr guest_block_start;
        Int insn_block_delta;
    } Insn_linear;


    class mem_trace {
    public:
        virtual void write( PAGE* unit, HWord ea, UInt size) { }
        virtual void read( PAGE* unit, HWord ea, UInt size) { }

        virtual void write(PAGE* unit, PAGE*next,  HWord ea, UInt size) { }
        virtual void read(PAGE* unit, PAGE* next, HWord ea, UInt size) { }
    };

    //memory base
    class MBase : public mapping<PAGE> {
        friend class StateBase;
    protected:
        std::atomic_uint32_t m_user;
        z3::vcontext& m_ctx;
        z3::solver&   m_solver;
        Insn_linear   m_insn_linear;
        Bool          m_need_record;

        MBase(z3::solver& s, z3::vcontext& ctx, PML4T** cr3, Int _user, Bool _need_record);
        MBase(z3::solver& so, z3::vcontext& ctx, Bool _need_record);
        MBase(z3::solver& so, z3::vcontext& ctx, MBase& father_mem, Bool _need_record);

        ~MBase() { recycle(); }

    public:

        inline Int get_user() { return m_user; }

        bool checkup_page_ref(PAGE*& P, PAGE** PT);
        PAGE* get_write_page(HWord addr);

        UInt write_bytes(ULong address, ULong length, UChar* data);
        virtual z3::expr idx2Value(Addr64 base, Z3_ast idx) { return z3::expr(m_ctx); };
        ULong find_block_forward(ULong start, HWord size);
        ULong find_block_reverse(ULong start, HWord size);


        //unsigned long long mem_real_hash(Addr guest_addr, unsigned length);

        //把两个不连续的页放到insn_linear里，以支持valgrind的跨页翻译
        //第一次调用
        const UChar* get_vex_insn_linear(Addr guest_IP_sbstart);

        //多次调用即返回线性地址
        //使用之必须调用 get_vex_insn_linear
        const UChar* libvex_guest_insn_control(Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code);

        inline const UChar* get_next_page(Addr32 address) {
            PAGE* P = get_mem_page(address + 0x1000);
            return P ? pto_data(P)->get_bytes(0) : nullptr;
        }

        inline const UChar* get_next_page(Addr64 address) {
            PAGE* P = get_mem_page(address + 0x1000);
            return P ? pto_data(P)->get_bytes(0) : nullptr;
        }

        inline operator Z3_context() const { return m_ctx; };
        inline operator z3::vcontext& () { return m_ctx; };
        inline z3::vcontext& ctx() { return m_ctx; };

        virtual PAGE* map_interface(ULong address) override;
    private:
        virtual void copy_interface(PAGE* pt_dst[1], PAGE* pt_src[1]) override;
        virtual void unmap_interface(PAGE* pt[1]) override;

    };



    static mem_trace default_trace;

    class Mem : public MBase {
        friend class vex_context;
        mem_trace* m_trace = &default_trace;

    public:


        class Itaddress {
        private:
            z3::solver& m_solver;
            z3::context& m_ctx;
            Z3_ast m_addr;
            Z3_ast last_avoid_addr;
            Z3_lbool m_lbool;
            //std::vector<Z3_model> v_model;
        public:
            Itaddress(z3::solver& s, Z3_ast addr, int wide) :m_solver(s), m_ctx(m_solver.ctx()), m_addr(addr) {
                m_addr = Z3_simplify(s.ctx(), m_addr);
                Z3_inc_ref(m_ctx, m_addr);
                m_solver.push();
                Z3_ast so = Z3_mk_bvule(m_ctx, m_addr, m_ctx.bv_val((HWord)-1, wide));
                Z3_inc_ref(m_ctx, so);
                Z3_solver_assert(m_ctx, m_solver, so);
                Z3_dec_ref(m_ctx, so);
                //v_model.reserve(20);
            }

            inline bool check() {
                m_lbool = Z3_solver_check(m_ctx, m_solver);
                vassert(m_lbool != Z3_L_UNDEF);
                return m_lbool == Z3_L_TRUE;
            }

            inline void operator++(int)
            {
                Z3_ast eq = Z3_mk_eq(m_ctx, m_addr, last_avoid_addr);
                Z3_inc_ref(m_ctx, eq);
                Z3_ast neq = Z3_mk_not(m_ctx, eq);
                Z3_inc_ref(m_ctx, neq);
                Z3_solver_assert(m_ctx, m_solver, neq);
                Z3_dec_ref(m_ctx, eq);
                Z3_dec_ref(m_ctx, neq);
                Z3_dec_ref(m_ctx, last_avoid_addr);
    }

            rsval<HWord> operator*()
            {
                Z3_model m_model = Z3_solver_get_model(m_ctx, m_solver); vassert(m_model);
                Z3_model_inc_ref(m_ctx, m_model);
                //v_model.emplace_back(m_model);
                Z3_ast r = 0;
                bool status = Z3_model_eval(m_ctx, m_model, m_addr, /*model_completion*/false, &r);
                vassert(status);
                Z3_inc_ref(m_ctx, r);
                last_avoid_addr = r;
                ULong ret;
                vassert(Z3_get_ast_kind(m_ctx, r) == Z3_NUMERAL_AST);
                vassert(Z3_get_numeral_uint64(m_ctx, r, &ret));
                Z3_model_dec_ref(m_ctx, m_model);
                return rsval<HWord>(m_ctx, ret, r);
            }
            inline ~Itaddress() {
                Z3_dec_ref(m_ctx, m_addr);
                m_solver.pop();
                //for (auto m : v_model) Z3_model_dec_ref(m_ctx, m);
            }
        };



    public:

        Mem(z3::solver& s, z3::vcontext& ctx, PML4T** cr3, Int _user, Bool _need_record) :
            MBase(s,ctx, cr3, _user, _need_record)
        { };

        Mem(z3::solver& so, z3::vcontext& ctx, Bool _need_record) :
            MBase(so, ctx, _need_record)
        {  }

        Mem(z3::solver& so, z3::vcontext& ctx, MBase& father_mem, Bool _need_record) :
            MBase(so, ctx, father_mem, _need_record)
        { ; }


        Itaddress addr_begin(z3::solver& s, Z3_ast addr, int wide) { return Itaddress(s, addr, wide); }

    private:
        sv::tval _Iex_Load(PAGE* P, HWord address, UShort size);

    public:
        void set_mem_traceer(mem_trace& t) { m_trace = &t; };
        //----------------------- real address -----------------------
        // load<sign, 32, Z3_BV_SORT>(HWord)
        template<bool sign, int nbits, sv::z3sk sk>
        inline sv::rsval<sign, nbits, sk> load(HWord address) {
            static_assert((nbits & 7) == 0, "err load");
            if ((address>>56)==1) {
                return sv::rsval<sign, nbits, sk>(m_ctx, (void*)(address & fastMask(56)));
            }
            PAGE* page = get_mem_page(address);
            MEM_ACCESS_ASSERT_R(page, address);
            if UNLIKELY((address & 0xfff) >= (0x1001 - (nbits >> 3))) {
                return _Iex_Load(page, address, nbits >> 3).template tors<sign, nbits, sk>();
            }
            if (page->is_data())
                return pto_data(page)->get_unit().load<sign, nbits, sk>(get_user(), (UInt)address & 0xfff, m_ctx);
            else
                return pto_padding(page)->load<sign, nbits, sk>((UInt)address & 0xfff, m_ctx);
        }

            // IRType  load<Ity_I32>(HWord)
            template<IRType ty, class _svc = sv::IRty<ty>>
            inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(HWord address) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
            }

            // load arithmetic   load<ULong>(HWord)
            template<typename ty, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
            inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(HWord address) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
            }

            //--------------------------- load ctype_val -----------------------------

            // load<IRType>(ctype_val)
            template<IRType ty, class _svc = sv::IRty<ty>, int ea_nbits>
            inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(sv::ctype_val<false, ea_nbits, Z3_BV_SORT> const& address) {
                return load<nbits, _svc::is_signed, _svc::nbits, _svc::sk>((HWord)address);
            }


            // load<ULong>(ctype_val)
            template<typename ty, class _svc = sv::sv_cty<ty>, int ea_nbits, TASSERT(sv::is_ret_type<ty>::value)>
            inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(sv::ctype_val<false, ea_nbits, Z3_BV_SORT> const& address) {
                return load<nbits, _svc::is_signed, _svc::nbits, _svc::sk>((HWord)address);
            }

        //----------------------- ast address -----------------------

        template<bool sign, int nbits, sv::z3sk sk, int ea_nbits>
        sv::rsval<sign, nbits, sk> load_all(const subval<ea_nbits>& address) {
            sv::symbolic<sign, nbits, sk> ret(m_ctx);
            bool first = true;
            {
                Itaddress it = this->addr_begin(m_solver, address, ea_nbits);
                while (it.check()) {
                    rsval<HWord> addr = *it;
                    sv::rsval<sign, nbits, sk>  data = load<sign, nbits, sk>((HWord)addr.tor());
                    if (first) {
                        first = false;
                        ret = data.tos();
                    }
                    else {
                        ret = ite(address == addr.tos(), data.tos(), ret);
                    }
                    it++;
                };
            }
            if (!(Z3_ast)ret) {
                throw Expt::SolverNoSolution("load error", m_solver);
            };
            return ret;
        }

        // load<sign, nbits, z3sk>(subval<ea_nbits>)
        template<bool sign, int nbits, sv::z3sk sk, int ea_nbits>
        inline sv::rsval<sign, nbits, sk> load(const subval<ea_nbits>& address) {
            static_assert((nbits & 7) == 0, "err load");
            //            TR::addressingMode<HWord> am(z3::expr(m_ctx, address));
            //            auto kind = am.analysis_kind();
            //            if (kind != TR::addressingMode<HWord>::cant_analysis) {
            //#ifdef TRACE_AM
            //                printf("Iex_Load  base: %p {\n", (void*)(size_t)am.getBase());
            //                am.print();
            //                printf("}\n");
            //                //am.print_offset();
            //#endif
            //                z3::expr tast = idx2Value(am.getBase(), am.getoffset());
            //                if ((Z3_ast)tast) {
            //                    return sv::rsval<sign, nbits, sk>(m_ctx, (Z3_ast)tast);
            //                }
            //                else {
            //                    if (kind == TR::addressingMode<HWord>::support_bit_blast) {
            //                        sv::symbolic<sign, nbits, sk> ret(m_ctx);
            //                        bool first = true;
            //                        for (typename TR::addressingMode<HWord>::iterator off_it = am.begin();
            //                            off_it.check();
            //                            off_it.next()) {
            //                            HWord offset = *off_it;
            //                            sv::rsval<sign, nbits, sk> data = load<sign, nbits, sk>(am.getBase() + offset);
            //
            //                            if (first) {
            //                                first = false;
            //                                ret = data.tos();
            //                            }
            //                            else {
            //                                sbool _if = subval<wide>(am.getoffset()) == offset;
            //                                ret = ite(_if, data.tos(), ret);
            //                            }
            //                        }
            //                        if (!(Z3_ast)ret) { throw Expt::SolverNoSolution("load error", m_solver); };
            //                        return ret;
            //                    }
            //                }
            //            }
            return load_all<sign, nbits, sk>(address);
        }

            // load<IRType>(subval<ea_nbits>)
            template<IRType ty, int ea_nbits, class _svc = sv::IRty<ty>>
            inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(const subval<ea_nbits>& address) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
            }

            // load<sign, nbits, z3sk>(z3::expr)
            template<bool sign, int nbits, sv::z3sk sk>
            inline sv::rsval<sign, nbits, sk> load(const z3::expr &address) {
                if (address.get_sort().bv_size() == 32) {
                    return load<sign, nbits, sk>(subval<32>(address));
                }
                else {
                    return load<sign, nbits, sk>(subval<64>(address));
                }
            }

                // load<sign, nbits, z3sk>(Z3_ast)
                template<bool sign, int nbits, sv::z3sk sk>
                inline sv::rsval<sign, nbits, sk> load(Z3_ast address) {
                    return load<sign, nbits, sk>(z3::expr(m_ctx, address));
                }

                    // IRType     load<IRType>(Z3_ast)
                    template<IRType ty, class _svc = sv::IRty<ty>>
                    inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(Z3_ast address) {
                        return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
                    }

                    // load arithmetic   load<ULong>(Z3_ast)
                    template<typename ty, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
                    inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(Z3_ast address) {
                        return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
                    }



        //--------------------------- load rsval -----------------------------

        template<bool sign, int nbits, sv::z3sk sk, int ea_nbits>
        inline sv::rsval<sign, nbits, sk> load(const sv::rsval<false, ea_nbits, Z3_BV_SORT>& address) {
            if LIKELY(address.real()) {
                return load<sign, nbits, sk>((HWord)address.tor());
            }
            else {
                return load<sign, nbits, sk>(address.tos());
            }
        }

            // load<IRType>(rsval)
            template<IRType ty, int ea_nbits, class _svc = sv::IRty<ty>>
            inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(const sv::rsval<false, ea_nbits, Z3_BV_SORT>& address) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
            }

            // load<ULong>(rsval)
            template<typename ty, int ea_nbits, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
            inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(const sv::rsval<false, ea_nbits, Z3_BV_SORT>& address) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
            }

            // load<sign, nbits, sk>(tval)
            template<bool sign, int nbits, sv::z3sk sk>
            inline sv::rsval<sign, nbits, sk> load(const sv::tval& address) {
                if (address.nbits() == 32) {
                    return load<sign, nbits, sk>(address.tors<false, 32, Z3_BV_SORT>());
                }
                else {
                    return load<sign, nbits, sk>(address.tors<false, 64, Z3_BV_SORT>());
                }
            }

                // load<IRType>(tval)
                template<IRType ty, class _svc = sv::IRty<ty> >
                inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(const sv::tval& address) {
                    return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
                }
        
                // load<ULong>(tval)
                template<typename ty, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
                inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(sv::tval const& address) {
                    return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
                }


        sv::tval Iex_Load(HWord address, IRType ty);
        template<int ea_nbits>
        sv::tval Iex_Load(const subval<ea_nbits>& address, IRType ty);
            inline sv::tval Iex_Load(const z3::expr& address, IRType ty) { if (address.get_sort().bv_size() == 32) { return Iex_Load(subval<32>(address), ty); } else { return Iex_Load(subval<64>(address), ty); }; }
                inline sv::tval Iex_Load(Z3_ast address, IRType ty) { return Iex_Load(z3::expr(m_ctx, address), ty); }
                sv::tval Iex_Load(const sv::tval& address, IRType ty);
        sv::tval Iex_Load(const sv::tval& address, int nbytes);
        template<int ea_nbits>
        inline sv::tval Iex_Load(const sv::rsval<false, ea_nbits>& address, IRType ty){
            if (address.real()) {
                return Iex_Load((HWord)address.tor(), ty);
            }
            else {
                return Iex_Load(address.tos(), ty);
            }
        }


        void storeR_between2page(HWord address, UInt offset, PAGE* page, UInt size_data, const void* data) {
            PAGE* npage = get_write_page(address + 0x1000);
            UInt plength = (0x1000 - offset);
            m_trace->write(page, npage, address, size_data);// trace
            pto_data(page)->get_unit().Ist_Put(offset, (void*)data, plength);
            pto_data(npage)->get_unit().Ist_Put(0, ((UChar*)((void*)data)) + plength, (size_data - plength));
        }

        void storeS_between2page(HWord address, UInt offset, PAGE* page, UInt size_data, Z3_ast data) {
            PAGE* npage = get_write_page(address + 0x1000);
            m_trace->write(page, npage, address, size_data);// trace
            UInt plength = (0x1000 - offset);
            Z3_ast Low = Z3_mk_extract(m_ctx, (plength << 3) - 1, 0, data);
            Z3_inc_ref(m_ctx, Low);
            Z3_ast HI = Z3_mk_extract(m_ctx, (size_data << 3) - 1, plength << 3, data);
            Z3_inc_ref(m_ctx, HI);
            pto_data(page)->get_unit().Ist_Put(offset, Low, plength);
            pto_data(npage)->get_unit().Ist_Put(0, HI, (size_data) - plength);
            Z3_dec_ref(m_ctx, Low);
            Z3_dec_ref(m_ctx, HI);
        }


        //----------------------- real addr store arithmetic-----------------------

        // store(HWord, ULong v)
        template<typename DataTy, TASSERT(std::is_arithmetic_v<DataTy>)>
        void store(HWord address, DataTy data) {
            static constexpr int nbytes = ALLOC_ALIGN_BIT(sizeof(DataTy) << 3, 3);
            PAGE* page = get_write_page(address);
            UShort offset = address & 0xfff;
            if UNLIKELY(nbytes > 0x1000 - offset) {
                storeR_between2page(address, offset, page, nbytes, &data);
            }
            else {
                m_trace->write(page, address, nbytes);// trace
                pto_data(page)->get_unit().set(offset, data);
            }
        }

        // store(HWord, const __m256i& v)
        template<typename DataTy, TASSERT(is_large_ctype_v<DataTy>)>
        void store(HWord address, const DataTy& data) {
            static constexpr int nbytes = ALLOC_ALIGN_BIT(sizeof(DataTy) << 3, 3);
            PAGE* page = get_write_page(address);
            UShort offset = address & 0xfff;
            if UNLIKELY(nbytes > 0x1000 - offset) {
                storeR_between2page(address, offset, page, nbytes, &data);
            }
            else {
                m_trace->write(page, address, nbytes);// trace
                pto_data(page)->get_unit().set(offset, data);
            }
        }


            // store(HWord, const ctype_val<sign, nbits>&)
            template<bool sign, int nbits, sv::z3sk sk>
            inline void store(HWord address, const sv::ctype_val<sign, nbits, sk>& data) { store(address, data.value()); }



        // store(HWord, const symbolic<sign, nbits>&)
        template<bool sign, int nbits, sv::z3sk sk>
        void store(HWord address, const sv::symbolic<sign, nbits, sk>& data) {
            static_assert((nbits & 7) == 0, " store(HWord, Z3_ast) ?");
            static constexpr int nbytes = ALLOC_ALIGN_BIT(nbits, 3);
            PAGE* page = get_write_page(address);
            UShort offset = address & 0xfff;
            if UNLIKELY(nbytes > 0x1000 - offset) {
                storeS_between2page(address, offset, page, nbytes, (Z3_ast)data);
            }
            else {
                m_trace->write(page, address, nbytes);// trace
                pto_data(page)->get_unit().set<nbits>(offset, data);
            }
        }


        template<bool sign, int nbits, sv::z3sk sk>
        inline void store(HWord address, const sv::rsval<sign, nbits, sk>& data) {
            if LIKELY(data.real()) {
                store(address, data.tor().value());
            }
            else {
                store(address, data.tos());
            }
        }

        //-----------------------  symbolic addr store  -----------------------

        // store(subval<ea_nbits>, symbolic)
        // symbolic symbolic
        template<bool sign, int nbits, sv::z3sk sk, int ea_nbits>
        void store(const subval<ea_nbits>& address, const sv::symbolic<sign, nbits, sk>& data) {
//            TR::addressingMode<HWord> am(z3::expr(m_ctx, address));
//            auto kind = am.analysis_kind();
            int count = 0;
//            if (kind == TR::addressingMode<HWord>::support_bit_blast) {
//#ifdef TRACE_AM
//                printf("Ist_Store base: %p {\n", (void*)(size_t)am.getBase());
//                am.print();
//                printf("}\n");
//#endif
//                for (typename TR::addressingMode<HWord>::iterator off_it = am.begin();
//                    off_it.check();
//                    off_it.next()) {
//                    count++;
//                    auto offset = *off_it;
//                    HWord raddr = am.getBase() + offset;
//                    auto oData = load<DataTy>(raddr);
//                    auto rData = ite(subval<wide>(am.getoffset()) == offset, sval<DataTy>(m_ctx, data), oData.tos());
//                    store(raddr, rData);
//                }
//            }
//            else {
                Itaddress it = this->addr_begin(m_solver, address, ea_nbits);
                while (it.check()) {
                    count++;
                    rsval<HWord> addr = *it;
                    HWord addr_re = addr.tor();
                    auto oData = load<sign, nbits, Z3_BV_SORT>(addr_re);
                    auto rData = ite(address == addr.tos(), data, oData.tos());
                    store(addr, rData);
                    it++;
                }
            //}
            if (!count) { throw Expt::SolverNoSolution("store error", m_solver); };
        }

        // symbolic DataType
        template<int ea_nbits, typename DataTy, TASSERT(!is_large_ctype_v<DataTy>)>
        inline void store(const subval<ea_nbits>& address, DataTy data) {
            store(address, sval<DataTy>(m_ctx, data));
        }
        // symbolic DataType
        template<int ea_nbits, typename DataTy, TASSERT(is_large_ctype_v<DataTy>)>
        inline void store(const subval<ea_nbits>& address, const DataTy& data) {
            store(address, sval<DataTy>(m_ctx, data));
        }
        // symbolic ctypeval
        template<int ea_nbits, bool sign, int nbits, sv::z3sk sk>
        inline void store(const subval<ea_nbits>& address, const sv::ctype_val<sign, nbits, sk>& data) {
            store(address, sv::symbolic<sign, nbits, sk>(data));
        }
        // symbolic rsval
        template<int ea_nbits, bool sign, int nbits, sv::z3sk sk>
        inline void store(const subval<ea_nbits>& address, const sv::rsval<sign, nbits, sk>& data) {
            if (data.real()) {
                store(address, data.tor());
            }
            else { 
                store(address, data.tos()); 
            };
        }

        //-----------------------  rsval addr store  -----------------------

        // rsval DataType symbolic ctypeval
        template<int ea_nbits, typename DataTy, TASSERT(!is_large_v<DataTy>)>
        inline void store(const sv::rsval<false, ea_nbits, Z3_BV_SORT>& address, DataTy data) {
            if LIKELY(address.real()) {
                store(address.tor().value(), data);
            }else {
                store(address.tos(), data);
            }
        }
        // rsval DataType symbolic ctypeval
        template<int ea_nbits, typename DataTy, TASSERT(is_large_v<DataTy>)>
        inline void store(const sv::rsval<false, ea_nbits, Z3_BV_SORT>& address, const DataTy& data) {
            if LIKELY(address.real()) {
                store(address.tor().value(), data);
            }else {
                store(address.tos(), data);
            }
        }

        // rsval rsval
        template<int ea_nbits, bool sign, int nbits, sv::z3sk sk>
        inline void store(const sv::rsval<false, ea_nbits, Z3_BV_SORT>& address, const sv::rsval<sign, nbits, sk>& data) {
            if LIKELY(data.real()) {
                store(address, data.tor());
            }else {
                store(address, data.tos());
            }
        }


        //-----------------------  Ist_Store  -----------------------
        
        void Ist_Store(HWord address, sv::tval const& data);
        template<int ea_nbits>
        void Ist_Store(const subval<ea_nbits>& address, sv::tval const& data);
        template<int ea_nbits>
        void Ist_Store(const sv::rsval<false, ea_nbits>& address, sv::tval const& data) {
            if (address.real()) { Ist_Store((HWord)address.tor(), data); }
            else { Ist_Store(address.tos(), data); }
        }

        void Ist_Store(sv::tval const& address, sv::tval const& data);


        void Ist_Store(const z3::expr& address, const sv::tval& data) { Ist_Store(sv::expr2tval(address), data); };

        void Ist_Store(Z3_ast address, const sv::tval& data) { Ist_Store(z3::expr(m_ctx, address), data); };


    };


};


//#endif //  MEMORY_DEFS_H
