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

//#include <Windows.h>
#include "engine/engine.h"
#include "engine/basic_var.hpp"
#include "engine/register.h"
#include "engine/state_class.h"
#include "engine/addressing_mode.h"
#include "engine/mem_map.h"





#ifdef _DEBUG
#define NEED_VERIFY 
#define TRACE_AM
#endif

constexpr double ANALYZER_TIMEOUT = 0.4;

#define LINETOSTR(A) #A
#define CONCATSTR(A, B) " ACCESS MEM ERR UNMAPPED; " A " AT Line: " LINETOSTR(B)

//客户机内存访问检查
#define MEM_ACCESS_ASSERT_R(CODE, HWordESS) if UNLIKELY(!(CODE)) throw Expt::GuestMemReadErr(CONCATSTR(__FILE__, __LINE__), HWordESS);
#define MEM_ACCESS_ASSERT_W(CODE, HWordESS) if UNLIKELY(!(CODE)) throw Expt::GuestMemWriteErr(CONCATSTR(__FILE__, __LINE__), HWordESS);

class PAGE_DATA;
class PAGE_PADDING;

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

    inline PAGE(Int u, PageTy mem_ty) : m_user(u), m_ref_cound(1), m_mem_ty(mem_ty){};
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

};

class TR::mem_unit : public TR::Register<0x1000> {
    Int m_user;
    using page_class = TR::Register<0x1000>;
    friend class PAGE_DATA;
    friend class PAGE_PADDING;

    inline mem_unit(Int u, z3::vcontext& ctx, Bool need_record) : page_class(ctx, need_record), m_user(u){ }
    inline mem_unit(Int u, z3::vcontext& ctx, Bool _need_record, UChar init_value) : page_class(ctx, _need_record), m_user(u) { memset(m_bytes, init_value, sizeof(m_bytes)); }
    //翻译转换父register
    inline mem_unit(Int u, TR::mem_unit& father_page, z3::vcontext& ctx, Bool need_record) : page_class((page_class&)father_page, ctx, need_record), m_user(u) { }
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

    inline tval Iex_Get(Int target_user, UInt offset, UInt nbytes, z3::vcontext& target_ctx) {
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
    TR::mem_unit m_unit;
    friend class TR::MEM;
    friend class TR::MEM_BASE;
    friend class PAGE_PADDING;
    inline PAGE_DATA(Int u,
        z3::vcontext& ctx, Bool need_record
    ) : PAGE(u, mem_DATA), m_unit(u, ctx, need_record) { }


    inline PAGE_DATA(Int u,
        z3::vcontext& ctx, Bool need_record, UChar init_value
    ) : PAGE(u, mem_DATA), m_unit(u, ctx, need_record, init_value) { }

    // translate
    inline PAGE_DATA(Int u,
        PAGE_DATA& father, z3::vcontext& ctx, Bool need_record
    ) : PAGE(u, mem_DATA), m_unit(u, father.get_unit(), ctx, need_record) { }

    TR::mem_unit& get_unit() { return m_unit; }
    const UChar* get_bytes(UInt offst) { return m_unit.get_bytes(offst); }

    inline bool is_code() = delete;
    inline bool is_data() = delete;
    inline bool is_padding() = delete;
};


// 该页是填充区
class PAGE_PADDING : public PAGE {
    UChar m_padding_value = 0xcc;
    __m256i m_padding;

    friend class PAGE_DATA;
    friend class TR::MEM;
    friend class TR::MEM_BASE;
    inline PAGE_PADDING(Int u, UChar pad_value) : PAGE(u, mem_PADDING), m_padding_value(pad_value) { m_padding = _mm256_set1_epi8(m_padding_value); }
public:
    template<bool sign, int nbits, sv::z3sk sk>
    inline sv::rsval<sign, nbits, sk> load(UInt idx, Z3_context target_ctx) {
        return sv::rsval<sign, nbits, sk>(target_ctx, (UChar*)&m_padding);
    }
    inline void set_padding_value(UChar v) { m_padding_value = v;  m_padding = _mm256_set1_epi8(v); }
    inline UChar get_padding_value() const { return m_padding_value; }
    static PAGE_DATA* convert_to_data(PAGE* pt[1]/*in&out*/, z3::vcontext& ctx, bool nr);

    inline bool is_code() = delete;
    inline bool is_data() = delete;
    inline bool is_padding() = delete;
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

    class MEM_BASE : public mapping<PAGE> {

    protected:
        HASH_MAP<HWord, mem_unit*> mem_change_map;
        TR::vctx_base&  m_vctx;
        Bool            need_record;
        Int             user;
        z3::vcontext&   m_ctx;
        z3::solver&     m_solver;
        EmuEnvironment* m_ee = nullptr;
        Insn_linear     m_insn_linear;

        MEM_BASE(TR::vctx_base& vctxb, z3::solver& s, z3::vcontext& ctx, PML4T** cr3, Int _user, Bool _need_record) :
            m_vctx(vctxb),
            need_record(_need_record),
            user(_user),
            m_ctx(ctx),
            m_solver(s)
        {
            CR3[0] = cr3[0];
        };


        MEM_BASE(vctx_base& vctx, z3::solver& so, z3::vcontext& ctx, Bool _need_record) :
            m_vctx(vctx),
            need_record(_need_record),
            user(vctx.mk_user_id()),
            m_ctx(ctx),
            m_solver(so)
        {
        }

        MEM_BASE(z3::solver& so, z3::vcontext& ctx, MEM_BASE& father_mem, Bool _need_record) :
            m_vctx(father_mem.m_vctx),
            m_ctx(ctx),
            need_record(_need_record),
            m_solver(so),
            user(m_vctx.mk_user_id())
        {
            vassert(this->user != father_mem.user);
            this->copy(father_mem.CR3[0]);
        }

    public:
        virtual PAGE* map_interface(ULong address) override;
        inline Int get_user() { return user; }

    private:
        virtual void copy_interface(PAGE* pt_dst[1], PAGE* pt_src[1]) override;
        virtual void unmap_interface(PAGE* pt[1]) override;

    public:
        bool checkup_page_ref(PAGE*& P, PAGE** PT);
        PAGE* get_write_page(HWord addr);

        UInt write_bytes(ULong address, ULong length, UChar* data);

        void set(EmuEnvironment* e) { m_ee = e; }
        virtual z3::expr idx2Value(Addr64 base, Z3_ast idx) { return z3::expr(m_ctx); };
        //清空写入记录
        void clearRecord();
        inline bool is_need_record() { return need_record; }
        ULong find_block_forward(ULong start, HWord size);
        ULong find_block_reverse(ULong start, HWord size);
        inline HASH_MAP<HWord, TR::mem_unit*> change_map() { return mem_change_map; }


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
    };


    class MEM : public MEM_BASE {
        friend class State;
        friend class ::DMem;
        template<typename _> friend class vex_context;
        // wide
        // static constexpr int wide = sizeof(HWord) << 3;

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
            Itaddress(z3::solver& s, Z3_ast addr) :m_solver(s), m_ctx(m_solver.ctx()), m_addr(addr) {
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


    private:
        inline MEM(TR::vctx_base& vctxb, z3::solver& s, z3::vcontext& ctx, PML4T** cr3, Int _user, Bool _need_record) :MEM_BASE(vctxb, s, ctx, cr3, _user, _need_record) {}

    public:
        MEM(TR::vctx_base& vctxb, z3::solver& so, z3::vcontext& ctx, Bool _need_record) :MEM_BASE(vctxb, so, ctx, _need_record) {};
        MEM(z3::solver& so, z3::vcontext& ctx, MEM& father_mem, Bool _need_record) : MEM_BASE(so, ctx, father_mem, _need_record) {};
        ~MEM() { recycle(); }

        Itaddress addr_begin(z3::solver& s, Z3_ast addr) { return Itaddress(s, addr); }

    private:
        tval _Iex_Load(PAGE* P, HWord address, UShort size);

    public:

        //----------------------- real address -----------------------

        template<bool sign, int nbits, sv::z3sk sk>
        inline sv::rsval<sign, nbits, sk> load(HWord address) {
            static_assert((nbits & 7) == 0, "err load");
            PAGE* page = get_mem_page(address);
            MEM_ACCESS_ASSERT_R(page, address);
            if UNLIKELY((address & 0xfff) >= (0x1001 - (nbits >> 3))) {
                return _Iex_Load(page, address, nbits >> 3).template tors<sign, nbits, sk>();
            }
            if(page->is_data())
                return pto_data(page)->get_unit().load<sign, nbits, sk>(get_user(), (UInt)address & 0xfff, m_ctx);
            else
                return pto_padding(page)->load<sign, nbits, sk>((UInt)address & 0xfff, m_ctx);
        }

        // IRType 
        template<IRType ty, class _svc = sv::IRty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(HWord address) {
            return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
        }

        // load arithmetic
        template<typename ty, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(HWord address) {
            return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
        }


        //----------------------- ast address -----------------------

        template<bool sign, int nbits, sv::z3sk sk>
        sv::rsval<sign, nbits, sk> load_all(const sval<HWord>& address) {
            sv::symbolic<sign, nbits, sk> ret(m_ctx);
            bool first = true;
            {
                Itaddress it = this->addr_begin(m_solver, address);
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


        template<bool sign, int nbits, sv::z3sk sk>
        inline sv::rsval<sign, nbits, sk> load(Z3_ast address) {
            static_assert((nbits & 7) == 0, "err load");
            TR::addressingMode<HWord> am(z3::expr(m_ctx, address));
            auto kind = am.analysis_kind();
            if (kind != TR::addressingMode<HWord>::cant_analysis) {
#ifdef TRACE_AM
                printf("Iex_Load  base: %p {\n", (void*)(size_t)am.getBase());
                am.print();
                printf("}\n");
                //am.print_offset();
#endif
                z3::expr tast = idx2Value(am.getBase(), am.getoffset());
                if ((Z3_ast)tast) {
                    return sv::rsval<sign, nbits, sk>(m_ctx, (Z3_ast)tast);
                }
                else {
                    if (kind == TR::addressingMode<HWord>::support_bit_blast) {
                        sv::symbolic<sign, nbits, sk> ret(m_ctx);
                        bool first = true;
                        for (typename TR::addressingMode<HWord>::iterator off_it = am.begin();
                            off_it.check();
                            off_it.next()) {
                            HWord offset = *off_it;
                            sv::rsval<sign, nbits, sk> data = load<sign, nbits, sk>(am.getBase() + offset);

                            if (first) {
                                first = false;
                                ret = data.tos();
                            }
                            else {
                                sbool _if = subval<wide>(am.getoffset()) == offset;
                                ret = ite(_if, data.tos(), ret);
                            }
                        }
                        if (!(Z3_ast)ret) { throw Expt::SolverNoSolution("load error", m_solver); };
                        return ret;
                    }
                }
            }
            return load_all<sign, nbits, sk>(sval<HWord>(m_ctx, address));
        }

        // IRType 
        template<IRType ty, class _svc = sv::IRty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(Z3_ast address) {
            return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
        }

        // load arithmetic
        template<typename ty, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(Z3_ast address) {
            return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
        }

        //--------------------------- load -----------------------------



        // load rsval
        template<IRType ty, bool _Ts, int nbits, class _svc = sv::IRty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(const sv::rsval<_Ts, nbits, Z3_BV_SORT>& address) {
            static_assert(nbits == wide, "err sz");
            if LIKELY(address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((HWord)address.tor());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos());
            }
        }

        // load rsval
        template<typename ty, bool _Ts, int nbits, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(const sv::rsval<_Ts, nbits, Z3_BV_SORT>& address) {
            static_assert(nbits == wide, "err sz");
            if LIKELY(address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((HWord)address.tor());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos());
            }
        }

        // load tval
        template<IRType ty, class _svc = sv::IRty<ty> >
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(tval const& address) {
            if LIKELY(address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((HWord)address.tor<false, wide>());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos<false, wide>());
            }
        }

        // load tval
        template<typename ty, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(tval const& address) {
            if LIKELY(address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((HWord)address.tor<false, wide>());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos<false, wide>());
            }
        }
        //ctype_val
        template<IRType ty, class _svc = sv::IRty<ty>, bool sign, int nbits>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(sv::ctype_val<sign, nbits, Z3_BV_SORT> const& address) {
            static_assert(nbits == wide, "err sz");
            if LIKELY(address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((HWord)address.tor<false, wide>());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos<false, wide>());
            }
        }
        // ctype_val
        template<typename ty, class _svc = sv::sv_cty<ty>, bool sign, int nbits, TASSERT(sv::is_ret_type<ty>::value)>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(sv::ctype_val<sign, nbits, Z3_BV_SORT> const& address) {
            static_assert(nbits == wide, "err sz");
            if LIKELY(address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((HWord)address.tor<false, wide>());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos<false, wide>());
            }
        }


        tval Iex_Load(Z3_ast address, IRType ty);
        tval Iex_Load(HWord address, IRType ty);
        tval Iex_Load(const tval& address, IRType ty);
        tval Iex_Load(const tval& address, int nbytes);
        tval Iex_Load(const sv::rsval<false, wide>& address, IRType ty);

        //----------------------- real addr store real -----------------------

        template<typename DataTy, TASSERT(std::is_arithmetic<DataTy>::value)>
        void store(HWord address, DataTy data) {
            PAGE* page = get_write_page(address);
            UShort offset = address & 0xfff;
            if UNLIKELY( ALLOC_ALIGN_BIT(sizeof(data) << 3,  3) > 0x1000 - offset) {
                PAGE* npage = get_write_page(address + 0x1000);
                UInt plength = (0x1000 - offset);
                pto_data(page)->get_unit().Ist_Put(offset, (void*)&data, plength);
                pto_data(npage)->get_unit().Ist_Put(0, ((UChar*)((void*)&data)) + plength, (sizeof(data) - plength));
            }
            else {
                pto_data(page)->get_unit().set(offset, data);
            }
        }


        //----------------------- real addr store simd -----------------------

        template<typename DataTy, TASSERT(sv::is_sse<DataTy>::value)>
        void store(HWord address, const DataTy& data) {
            PAGE* page = get_write_page(address);
            UShort offset = address & 0xfff;
            if UNLIKELY(ALLOC_ALIGN_BIT(sizeof(data) << 3, 3)> 0x1000 - offset) {
                PAGE* npage = get_write_page(address + 0x1000);
                UInt plength = (0x1000 - offset);
                pto_data(page)->get_unit().Ist_Put(offset, (void*)&data, plength);
                pto_data(npage)->get_unit().Ist_Put(0, ((UChar*)((void*)&data)) + plength, (sizeof(data) - plength));
            }
            else {
                pto_data(page)->get_unit().set(offset, data);
            }
        }

        //----------------------- real addr store ast -----------------------

        // only n_bit 8, 16, 32, 64 ,128 ,256
        template<int nbits>
        inline void store(HWord address, Z3_ast data) {
            static_assert((nbits & 7) == 0, "err store");
            PAGE* page = get_write_page(address);
            UShort offset = address & 0xfff;
            if UNLIKELY(ALLOC_ALIGN_BIT(nbits, 3) > 0x1000 - offset) {
                PAGE* npage = get_write_page(address + 0x1000);
                UInt plength = (0x1000 - offset);
                Z3_ast Low = Z3_mk_extract(m_ctx, (plength << 3) - 1, 0, data);
                Z3_inc_ref(m_ctx, Low);
                Z3_ast HI = Z3_mk_extract(m_ctx, nbits - 1, plength << 3, data);
                Z3_inc_ref(m_ctx, HI);
                pto_data(page)->get_unit().Ist_Put(offset, Low, plength);
                pto_data(npage)->get_unit().Ist_Put(0, HI, (nbits >> 3) - plength);
                Z3_dec_ref(m_ctx, Low);
                Z3_dec_ref(m_ctx, HI);
            }
            else {
                pto_data(page)->get_unit().set<nbits>(offset, data);
            }
        }

        //-----------------------  ast addr store real&&simd  -----------------------

        template<typename DataTy, TASSERT(std::is_arithmetic<DataTy>::value || sv::is_sse<DataTy>::value)>
        void store(Z3_ast address, DataTy data) {
            TR::addressingMode<HWord> am(z3::expr(m_ctx, address));
            auto kind = am.analysis_kind();
            int count = 0;
            if (kind == TR::addressingMode<HWord>::support_bit_blast) {
#ifdef TRACE_AM
                printf("Ist_Store base: %p {\n", (void*)(size_t)am.getBase());
                am.print();
                printf("}\n");
#endif
                for (typename TR::addressingMode<HWord>::iterator off_it = am.begin();
                    off_it.check();
                    off_it.next()) {
                    count++;
                    auto offset = *off_it;
                    HWord raddr = am.getBase() + offset;
                    auto oData = load<DataTy>(raddr);
                    auto rData = ite(subval<wide>(am.getoffset()) == offset, sval<DataTy>(m_ctx, data), oData.tos());
                    store(raddr, rData);
                }
            }
            else {
                Itaddress it = this->addr_begin(m_solver, address);
                while (it.check()) {
                    count++;
                    rsval<HWord> addr = *it;
                    HWord addr_re = addr.tor();
                    auto oData = load<DataTy>(addr_re);
                    auto rData = ite(subval<wide>(m_ctx, address) == addr.tos(), sval<DataTy>(m_ctx, data), oData.tos());
                    store(addr, rData);
                    it++;
                }
            }
            if (!count) { throw Expt::SolverNoSolution("store error", m_solver); };
        }

        //-----------------------  ast addr store ast -----------------------

        template<int nbits>
        void store(Z3_ast address, Z3_ast data) {
            static_assert((nbits & 7) == 0, "err store");
            TR::addressingMode<HWord> am(z3::expr(m_ctx, address));
            auto kind = am.analysis_kind();
            int count = 0;
            if (kind == TR::addressingMode<HWord>::support_bit_blast) {
#ifdef TRACE_AM
                printf("Ist_Store base: %p {\n", (void*)(size_t)am.getBase());
                am.print();
                printf("}\n");
#endif
                for (typename TR::addressingMode<HWord>::iterator off_it = am.begin();
                    off_it.check();
                    off_it.next()) {
                    count++;
                    HWord offset = *off_it;
                    HWord raddr = am.getBase() + offset;
                    auto oData = load<(IRType)nbits>(raddr);
                    auto rData = ite(subval<wide>(am.getoffset()) == offset, subval<nbits>(m_ctx, data), oData.tos());
                    store(raddr, rData);
                }
            }
            else {
                Itaddress it = this->addr_begin(m_solver, address);
                while (it.check()) {
                    count++;
                    rsval<HWord> addr = *it;
                    auto oData = load<(IRType)nbits>(addr);
                    auto rData = ite(subval<wide>(m_ctx, address) == addr.tos(), subval<nbits>(m_ctx, data), oData.tos());
                    store(addr, rData);
                    it++;
                }
            }
            if (!count) { throw Expt::SolverNoSolution("store error", m_solver); };
        }


        template<bool sign, int nbits, TASSERT(nbits <= 64)>
        inline void store(HWord address, const sv::ctype_val<sign, nbits, Z3_BV_SORT>& data) {
            store(address, data.value());
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(HWord address, const sv::symbolic<sign, nbits, Z3_BV_SORT>& data) {
            store<nbits>(address, (Z3_ast)data);
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(HWord address, const sv::rsval<sign, nbits, Z3_BV_SORT>& data) {
            if LIKELY(data.real()) {
                store(address, data.tor());
            }
            else {
                store<nbits>(address, (Z3_ast)data.tos());
            }
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(Z3_ast address, const sv::rsval<sign, nbits, Z3_BV_SORT>& data) {
            if LIKELY(data.real()) {
                store(address, data.tor().value());
            }
            else {
                store<nbits>(address, (Z3_ast)data.tos());
            }
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(const sv::rsval<false, wide, Z3_BV_SORT>& address, const sv::rsval<sign, nbits, Z3_BV_SORT>& data) {
            if LIKELY(address.real()) {
                store((HWord)address.tor(), data);
            }
            else {
                store((Z3_ast)address.tos(), data);
            }
        }


        template<typename DataTy, TASSERT(std::is_arithmetic<DataTy>::value || sv::is_sse<DataTy>::value)>
        inline void store(const sv::rsval<false, wide, Z3_BV_SORT>& address, DataTy data) {
            if LIKELY(address.real()) {
                store((HWord)address.tor(), data);
            }
            else {
                store((Z3_ast)address.tos(), data);
            }
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(const sv::rsval<false, wide, Z3_BV_SORT>& address, const sv::symbolic<sign, nbits, Z3_BV_SORT>& data) {
            if LIKELY(address.real()) {
                store<nbits>((HWord)address.tor(), (Z3_ast)data);
            }
            else {
                store<nbits>((Z3_ast)address.tos(), (Z3_ast)data);
            }
        }

        inline void Ist_Store(tval const& address, tval const& data) {
            if LIKELY(address.real()) {
                Ist_Store((HWord)address.tor<false, wide>(), data);
            }
            else {
                Ist_Store((Z3_ast)address.tos<false, wide>(), data);
            }
        }

        void Ist_Store(HWord address, tval const& data);
        void Ist_Store(Z3_ast address, tval const& data);
        

    };
};

#ifndef UNDEFMEM
#undef pto_data
#undef pto_padding
#undef GETPT
#undef GETPAGE
#undef COPY_SYM
#undef LCODEDEF1
#undef LCODEDEF2
#undef LCODEDEF3
#undef LCODEDEF4
#undef LCODEDEF5
#undef LMAX1
#undef LMAX2
#undef LMAX3
#undef LMAX4
#undef LMAX5
#undef LIND1
#undef LIND2
#undef LIND3
#undef LIND4
#undef LTAB1
#undef LTAB2
#undef LTAB3
#undef LTAB4
#undef LTAB5
#undef LSTRUCT1
#undef LSTRUCT2
#undef LSTRUCT3
#undef LSTRUCT4
#undef LSTRUCT5
#undef LINETOSTR
#undef CONCATSTR
#undef MEMACCESSERR
#endif

//#endif //  MEMORY_DEFS_H
