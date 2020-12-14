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
#ifndef MEMORY_DEFS_H
#define MEMORY_DEFS_H

//#include <Windows.h>
#include "engine/engine.h"
#include "engine/basic_var.hpp"
#include "engine/register.h"
#include "engine/state_class.h"
#include "engine/addressing_mode.h"
#include "engine/mem_map.h"


#define fastMaskI1(n) fastMask(((n)+1))
#define fastMaskReverseI1(N) (~fastMaskI1(N))

#define LZDEF(n) ((unsigned char)(((((((int)(n))-1) & -8) + 8) >> 3) - 1))
const UChar fastalignD1[257] = { LZDEF(0),  LZDEF(1),  LZDEF(2),  LZDEF(3),  LZDEF(4),  LZDEF(5),  LZDEF(6),  LZDEF(7),  LZDEF(8),  LZDEF(9),  LZDEF(10),  LZDEF(11),  LZDEF(12),  LZDEF(13),  LZDEF(14),  LZDEF(15),  LZDEF(16),  LZDEF(17),  LZDEF(18),  LZDEF(19),  LZDEF(20),  LZDEF(21),  LZDEF(22),  LZDEF(23),  LZDEF(24),  LZDEF(25),  LZDEF(26),  LZDEF(27),  LZDEF(28),  LZDEF(29),  LZDEF(30),  LZDEF(31),  LZDEF(32),  LZDEF(33),  LZDEF(34),  LZDEF(35),  LZDEF(36),  LZDEF(37),  LZDEF(38),  LZDEF(39),  LZDEF(40),  LZDEF(41),  LZDEF(42),  LZDEF(43),  LZDEF(44),  LZDEF(45),  LZDEF(46),  LZDEF(47),  LZDEF(48),  LZDEF(49),  LZDEF(50),  LZDEF(51),  LZDEF(52),  LZDEF(53),  LZDEF(54),  LZDEF(55),  LZDEF(56),  LZDEF(57),  LZDEF(58),  LZDEF(59),  LZDEF(60),  LZDEF(61),  LZDEF(62),  LZDEF(63),  LZDEF(64),  LZDEF(65),  LZDEF(66),  LZDEF(67),  LZDEF(68),  LZDEF(69),  LZDEF(70),  LZDEF(71),  LZDEF(72),  LZDEF(73),  LZDEF(74),  LZDEF(75),  LZDEF(76),  LZDEF(77),  LZDEF(78),  LZDEF(79),  LZDEF(80),  LZDEF(81),  LZDEF(82),  LZDEF(83),  LZDEF(84),  LZDEF(85),  LZDEF(86),  LZDEF(87),  LZDEF(88),  LZDEF(89),  LZDEF(90),  LZDEF(91),  LZDEF(92),  LZDEF(93),  LZDEF(94),  LZDEF(95),  LZDEF(96),  LZDEF(97),  LZDEF(98),  LZDEF(99),  LZDEF(100),  LZDEF(101),  LZDEF(102),  LZDEF(103),  LZDEF(104),  LZDEF(105),  LZDEF(106),  LZDEF(107),  LZDEF(108),  LZDEF(109),  LZDEF(110),  LZDEF(111),  LZDEF(112),  LZDEF(113),  LZDEF(114),  LZDEF(115),  LZDEF(116),  LZDEF(117),  LZDEF(118),  LZDEF(119),  LZDEF(120),  LZDEF(121),  LZDEF(122),  LZDEF(123),  LZDEF(124),  LZDEF(125),  LZDEF(126),  LZDEF(127),  LZDEF(128),  LZDEF(129),  LZDEF(130),  LZDEF(131),  LZDEF(132),  LZDEF(133),  LZDEF(134),  LZDEF(135),  LZDEF(136),  LZDEF(137),  LZDEF(138),  LZDEF(139),  LZDEF(140),  LZDEF(141),  LZDEF(142),  LZDEF(143),  LZDEF(144),  LZDEF(145),  LZDEF(146),  LZDEF(147),  LZDEF(148),  LZDEF(149),  LZDEF(150),  LZDEF(151),  LZDEF(152),  LZDEF(153),  LZDEF(154),  LZDEF(155),  LZDEF(156),  LZDEF(157),  LZDEF(158),  LZDEF(159),  LZDEF(160),  LZDEF(161),  LZDEF(162),  LZDEF(163),  LZDEF(164),  LZDEF(165),  LZDEF(166),  LZDEF(167),  LZDEF(168),  LZDEF(169),  LZDEF(170),  LZDEF(171),  LZDEF(172),  LZDEF(173),  LZDEF(174),  LZDEF(175),  LZDEF(176),  LZDEF(177),  LZDEF(178),  LZDEF(179),  LZDEF(180),  LZDEF(181),  LZDEF(182),  LZDEF(183),  LZDEF(184),  LZDEF(185),  LZDEF(186),  LZDEF(187),  LZDEF(188),  LZDEF(189),  LZDEF(190),  LZDEF(191),  LZDEF(192),  LZDEF(193),  LZDEF(194),  LZDEF(195),  LZDEF(196),  LZDEF(197),  LZDEF(198),  LZDEF(199),  LZDEF(200),  LZDEF(201),  LZDEF(202),  LZDEF(203),  LZDEF(204),  LZDEF(205),  LZDEF(206),  LZDEF(207),  LZDEF(208),  LZDEF(209),  LZDEF(210),  LZDEF(211),  LZDEF(212),  LZDEF(213),  LZDEF(214),  LZDEF(215),  LZDEF(216),  LZDEF(217),  LZDEF(218),  LZDEF(219),  LZDEF(220),  LZDEF(221),  LZDEF(222),  LZDEF(223),  LZDEF(224),  LZDEF(225),  LZDEF(226),  LZDEF(227),  LZDEF(228),  LZDEF(229),  LZDEF(230),  LZDEF(231),  LZDEF(232),  LZDEF(233),  LZDEF(234),  LZDEF(235),  LZDEF(236),  LZDEF(237),  LZDEF(238),  LZDEF(239),  LZDEF(240),  LZDEF(241),  LZDEF(242),  LZDEF(243),  LZDEF(244),  LZDEF(245),  LZDEF(246),  LZDEF(247),  LZDEF(248),  LZDEF(249),  LZDEF(250),  LZDEF(251),  LZDEF(252),  LZDEF(253),  LZDEF(254),  LZDEF(255),  LZDEF(256) };
#undef  LZDEF



#ifdef _DEBUG
#define NEED_VERIFY 
#define TRACE_AM
#endif

#define ANALYZER_TIMEOUT 0.4d

#define LINETOSTR(A) #A
#define CONCATSTR(A, B) " ACCESS MEM ERR UNMAPPED; " A " AT Line: " LINETOSTR(B)

//客户机内存访问检查
#define MEM_ACCESS_ASSERT_R(CODE, THwordESS) if (!(CODE)) throw Expt::GuestMemReadErr(CONCATSTR(__FILE__, __LINE__), THwordESS);
#define MEM_ACCESS_ASSERT_W(CODE, THwordESS) if (!(CODE)) throw Expt::GuestMemWriteErr(CONCATSTR(__FILE__, __LINE__), THwordESS);

//检查是否将ir translate的block区代码修改了，避免某些vmp或者ctf的恶作剧
#define CODEBLOCKISWRITECHECK(address) if(m_ee) m_ee->block_integrity(address, this->m_insn_linear.insn_block_delta);



class PAGE {
    Int _m_user_;
    Int m_user;
    std::atomic_int m_ref_cound;
    UChar m_pad = 0xcc;
    UChar m_is_pad = true;
    TR::Register<0x1000>* m_unit = nullptr;
public:
    inline bool is_pad() { return m_is_pad; };
    inline PAGE(Int u) :_m_user_(u), m_user(u), m_ref_cound(1){};
    inline Int get_user() const { return _m_user_; };
    inline UChar get_pad() const { return m_pad; };
    inline void set_pad(UChar pad) { 
        m_pad = pad; m_is_pad = true;
        vassert(!m_unit);
    };
    void copy(PAGE const* P, z3::vcontext& ctx, bool nr) {
        if (P->m_is_pad) {// 该页是填充区，则开始分配该页
            vassert(P->m_unit == NULL);
            m_unit = new TR::Register<0x1000>(ctx, nr);
            //memset(m_unit->m_bytes, P->m_pad, 0x1000);
        }
        else {
            m_unit = new TR::Register<0x1000>(*(P->m_unit), ctx, nr);
        }
        m_is_pad = false;
    }
    inline void disable_pad(z3::vcontext& ctx, bool nr) {
        // 该页是填充区，则开始分配该页
        if (m_is_pad) {
            vassert(m_unit == NULL);
            m_unit = new TR::Register<0x1000>(ctx, nr);
            //memset(m_unit->m_bytes, m_pad, 0x1000);
            m_is_pad = false;
        }
    }
    inline void malloc_unit(z3::vcontext& ctx, bool nr) {
        // 该页是填充区，则开始分配该页
        if (m_is_pad) {
            vassert(m_unit == NULL);
            m_unit = new TR::Register<0x1000>(ctx, nr);
            m_is_pad = false;
        }
    }
    inline  TR::Register<0x1000>* operator->() { return m_unit; }
    inline  operator TR::Register<0x1000>* () { return m_unit; }
    template<int MAX>
    void mount_regs(TR::Register<MAX>* s) {
        if (m_is_pad) {
            m_is_pad = false;
        }
        m_unit = (TR::Register<0x1000>*)s;
    }
    inline void lock(Int& xchg_user) {
        xchg_user = 0;
        while (!xchg_user) {
            __asm__ __volatile(
                "xchgl %0,%1"
                : "=r"(xchg_user) 
                : "m"(m_user), "0"(xchg_user) 
                : "memory");
        }
    }
    inline void unlock(Int xchg_user) {
        vassert(xchg_user == _m_user_);
        m_user = xchg_user;
    }

    inline void inc_used_ref() {
        vassert(m_ref_cound);
        m_ref_cound++;
    }

    inline bool dec_used_ref() {
        vassert(m_ref_cound);
        if (--m_ref_cound) {
            return True;
        }
        else {
            return False;
        }
    }

    inline void check_ref_cound() {
        vassert(m_ref_cound == 1);
    }

    template<bool sign, int nbits, sv::z3sk sk>
    inline sv::rsval<sign, nbits, sk> value(Z3_context ctx) {
        __m256i pad = _mm256_set1_epi8(m_pad);
        return sv::rsval<sign, nbits, sk>(ctx, M256i(pad).m256i_i8);
    };

    ~PAGE() noexcept(false) {
        vassert(m_ref_cound == 0); 
        if (m_unit) {
            delete m_unit;
        }
    }
};

class DMem;

namespace TR {
    typedef enum {
        enough,
        swap_state,
        next_page
    }Insn_linear_flag;

    typedef struct __declspec(align(16)) {
        unsigned char swap[32];
        Insn_linear_flag flag;
        UInt the_rest_n;
        const UChar* guest_addr_in_page;
        Addr guest_block_start;
        Int insn_block_delta;
    } Insn_linear;

    template<typename THword>
    class MEM : public mapping<PAGE> {
        friend class State<THword>;
        friend class ::DMem;
        template<typename _> friend class vex_context;
        //wide
        static constexpr int wide = sizeof(THword) << 3;
        
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
                Z3_ast so = Z3_mk_bvule(m_ctx, m_addr, m_ctx.bv_val((THword)-1, wide));
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

            rsval<THword> operator*()
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
                return rsval<THword>(m_ctx, ret, r);
            }
            inline ~Itaddress() {
                Z3_dec_ref(m_ctx, m_addr);
                m_solver.pop();
                //for (auto m : v_model) Z3_model_dec_ref(m_ctx, m);
            }
        };
    private:
        HASH_MAP<THword, TR::Register<0x1000>*> mem_change_map;
        TR::vctx_base&  m_vctx;
        Bool            need_record;
        Int             user;
        z3::vcontext&   m_ctx;
        z3::solver&     m_solver;
        EmuEnvironment<MAX_IRTEMP>* m_ee = nullptr;
        Insn_linear     m_insn_linear;

        virtual PAGE* map_interface(ULong address) override;
        virtual void copy_interface(PAGE* pt_dst[1], PAGE* pt_src[1]) override;
        virtual void unmap_interface(PAGE* pt[1]) override;

    private:
        bool check_page(PAGE*& P, PAGE** PT);
        PAGE* get_write_page(THword addr);
        tval _Iex_Load(PAGE* P, THword address, UShort size);
        void init_page(PAGE*& P, THword address);
        UInt write_bytes(ULong address, ULong length, UChar* data);
        MEM(TR::vctx_base & vctxb, z3::solver& s, z3::vcontext& ctx, PML4T** cr3, Int _user, Bool _need_record) :
            m_vctx(vctxb),
            need_record(_need_record),
            user(_user),
            m_solver(s),
            m_ctx(ctx)
        {
            CR3[0] = cr3[0];
        };

    public:
        MEM(TR::vctx_base& vctxb, z3::solver& so, z3::vcontext& ctx, Bool _need_record);
        MEM(z3::solver& so, z3::vcontext& ctx, MEM& father_mem, Bool _need_record);
        ~MEM() { recycle(); }
        void set(EmuEnvironment<MAX_IRTEMP>* e) { m_ee = e; }
        virtual z3::expr idx2Value(Addr64 base, Z3_ast idx) { return z3::expr(m_ctx); };
        //清空写入记录
        void clearRecord();
        ULong find_block_forward(ULong start, THword size);
        ULong find_block_reverse(ULong start, THword size);
        inline HASH_MAP<THword, TR::Register<0x1000>*> change_map() { return mem_change_map; }
        inline Int get_user() { return user; }


        //把两个不连续的页放到insn_linear里，以支持valgrind的跨页翻译
        //第一次调用
        const UChar* get_vex_insn_linear(Addr guest_IP_sbstart);

        //多次调用即返回线性地址
        //使用之必须调用 get_vex_insn_linear
        const UChar* libvex_guest_insn_control(Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code);

        inline UChar* get_next_page(Addr32 address) {
            PAGE* P = get_mem_page(address + 0x1000);
            return P ? (*P)->m_bytes : nullptr;
        }

        inline UChar* get_next_page(Addr64 address) {
            PAGE* P = get_mem_page(address + 0x1000);
            return P ? (*P)->m_bytes : nullptr;
        }
        Itaddress addr_begin(z3::solver& s, Z3_ast addr) { return Itaddress(s, addr); }

    public:

        //----------------------- real address -----------------------

        template<bool sign, int nbits, sv::z3sk sk>
        inline sv::rsval<sign, nbits, sk> load(THword address) {
            static_assert((nbits & 7) == 0, "err load");
            PAGE* page = get_mem_page(address);
            MEM_ACCESS_ASSERT_R(page, address);
            if (page->is_pad()) {
                return page->value<sign, nbits, sk>(m_ctx);
            };

            if ((address & 0xfff) >= (0x1001 - (nbits >> 3))) {
                return _Iex_Load(page, address, nbits >> 3).template tors<sign, nbits, sk>();
            }

            if (user == page->get_user()) {
                return (*page)->get<sign, nbits, sk>(address & 0xfff);
            }
            else {
                return (*page)->get<sign, nbits, sk >(address & 0xfff, m_ctx);
            }
        }

        // IRType 
        template<IRType ty, class _svc = sv::IRty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(THword address) {
            return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
        }

        // load arithmetic
        template<typename ty, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(THword address) {
            return load<_svc::is_signed, _svc::nbits, _svc::sk>(address);
        }


        //----------------------- ast address -----------------------

        template<bool sign, int nbits, sv::z3sk sk>
        sv::rsval<sign, nbits, sk> load_all(const sval<THword>& address) {
            sv::symbolic<sign, nbits, sk> ret(m_ctx);
            bool first = true;
            {
                Itaddress it = this->addr_begin(m_solver, address);
                while (it.check()) {
                    rsval<THword> addr = *it;
                    sv::rsval<sign, nbits, sk>  data = load<sign, nbits, sk>((THword)addr.tor());
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
            TR::addressingMode<THword> am(z3::expr(m_ctx, address));
            auto kind = am.analysis_kind();
            if (kind != TR::addressingMode<THword>::cant_analysis) {
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
                    if (kind == TR::addressingMode<THword>::support_bit_blast) {
                        sv::symbolic<sign, nbits, sk> ret(m_ctx);
                        bool first = true;
                        for (typename TR::addressingMode<THword>::iterator off_it = am.begin();
                            off_it.check();
                            off_it.next()) {
                            THword offset = *off_it;
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
            return load_all<sign, nbits, sk>(sval<THword>(m_ctx, address));
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
            if (address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((THword)address.tor());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos());
            }
        }

        // load rsval
        template<typename ty, bool _Ts, int nbits, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(const sv::rsval<_Ts, nbits, Z3_BV_SORT>& address) {
            static_assert(nbits == wide, "err sz");
            if (address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((THword)address.tor());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos());
            }
        }

        // load tval
        template<IRType ty, class _svc = sv::IRty<ty> >
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(tval const& address) {
            if (address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((THword)address.tor<false, wide>());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos<false, wide>());
            }
        }

        // load tval
        template<typename ty, class _svc = sv::sv_cty<ty>, TASSERT(sv::is_ret_type<ty>::value)>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(tval const& address) {
            if (address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((THword)address.tor<false, wide>());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos<false, wide>());
            }
        }
        //ctype_val
        template<IRType ty, class _svc = sv::IRty<ty>, bool sign, int nbits>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(sv::ctype_val<sign, nbits, Z3_BV_SORT> const& address) {
            static_assert(nbits == wide, "err sz");
            if (address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((THword)address.tor<false, wide>());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos<false, wide>());
            }
        }
        // ctype_val
        template<typename ty, class _svc = sv::sv_cty<ty>, bool sign, int nbits, TASSERT(sv::is_ret_type<ty>::value)>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> load(sv::ctype_val<sign, nbits, Z3_BV_SORT> const& address) {
            static_assert(nbits == wide, "err sz");
            if (address.real()) {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((THword)address.tor<false, wide>());
            }
            else {
                return load<_svc::is_signed, _svc::nbits, _svc::sk>((Z3_ast)address.tos<false, wide>());
            }
        }


        tval Iex_Load(Z3_ast address, IRType ty);
        tval Iex_Load(THword address, IRType ty);
        tval Iex_Load(const tval& address, IRType ty);
        tval Iex_Load(const tval& address, int nbytes);
        tval Iex_Load(const sv::rsval<false, wide>& address, IRType ty);

        //----------------------- real addr store real -----------------------

        template<typename DataTy, TASSERT(std::is_arithmetic<DataTy>::value)>
        void store(THword address, DataTy data) {
            PAGE* page = get_write_page(address);
            UShort offset = address & 0xfff;
            if (fastalignD1[sizeof(data) << 3] > 0xFFF - offset) {
                PAGE* npage = get_write_page(address + 0x1000);
                UInt plength = (0x1000 - offset);
                (*page)->Ist_Put(offset, (void*)&data, plength);
                (*npage)->Ist_Put(0, ((UChar*)((void*)&data)) + plength, (sizeof(data) - plength));
            }
            else {
                (*page)->set(offset, data);
            }
        }


        //----------------------- real addr store simd -----------------------

        template<typename DataTy, TASSERT(sv::is_sse<DataTy>::value)>
        void store(THword address, const DataTy& data) {
            PAGE* page = get_write_page(address);
            UShort offset = address & 0xfff;
            if (fastalignD1[sizeof(data) << 3] > 0xFFF - offset) {
                PAGE* npage = get_write_page(address + 0x1000);
                UInt plength = (0x1000 - offset);
                (*page)->Ist_Put(offset, (void*)&data, plength);
                (*npage)->Ist_Put(0, ((UChar*)((void*)&data)) + plength, (sizeof(data) - plength));
            }
            else {
                (*page)->set(offset, data);
            }
        }

        //----------------------- real addr store ast -----------------------

        // only n_bit 8, 16, 32, 64 ,128 ,256
        template<int nbits>
        inline void store(THword address, Z3_ast data) {
            static_assert((nbits & 7) == 0, "err store");
            PAGE* page = get_write_page(address);
            UShort offset = address & 0xfff;
            if (fastalignD1[nbits] > 0xFFF - offset) {
                PAGE* npage = get_write_page(address + 0x1000);
                UInt plength = (0x1000 - offset);
                Z3_ast Low = Z3_mk_extract(m_ctx, (plength << 3) - 1, 0, data);
                Z3_inc_ref(m_ctx, Low);
                Z3_ast HI = Z3_mk_extract(m_ctx, nbits - 1, plength << 3, data);
                Z3_inc_ref(m_ctx, HI);
                (*page)->Ist_Put(offset, Low, plength);
                (*npage)->Ist_Put(0, HI, (nbits >> 3) - plength);
                Z3_dec_ref(m_ctx, Low);
                Z3_dec_ref(m_ctx, HI);
            }
            else {
                (*page)->set<nbits>(offset, data);
            }
        }

        //-----------------------  ast addr store real&&simd  -----------------------

        template<typename DataTy, TASSERT(std::is_arithmetic<DataTy>::value || sv::is_sse<DataTy>::value)>
        void store(Z3_ast address, DataTy data) {
            TR::addressingMode<THword> am(z3::expr(m_ctx, address));
            auto kind = am.analysis_kind();
            int count = 0;
            if (kind == TR::addressingMode<THword>::support_bit_blast) {
#ifdef TRACE_AM
                printf("Ist_Store base: %p {\n", (void*)(size_t)am.getBase());
                am.print();
                printf("}\n");
#endif
                for (typename TR::addressingMode<THword>::iterator off_it = am.begin();
                    off_it.check();
                    off_it.next()) {
                    count++;
                    auto offset = *off_it;
                    THword raddr = am.getBase() + offset;
                    auto oData = load<DataTy>(raddr);
                    auto rData = ite(subval<wide>(am.getoffset()) == offset, sval<DataTy>(m_ctx, data), oData.tos());
                    store(raddr, rData);
                }
            }
            else {
                Itaddress it = this->addr_begin(m_solver, address);
                while (it.check()) {
                    count++;
                    rsval<THword> addr = *it;
                    THword addr_re = addr.tor();
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
            TR::addressingMode<THword> am(z3::expr(m_ctx, address));
            auto kind = am.analysis_kind();
            int count = 0;
            if (kind == TR::addressingMode<THword>::support_bit_blast) {
#ifdef TRACE_AM
                printf("Ist_Store base: %p {\n", (void*)(size_t)am.getBase());
                am.print();
                printf("}\n");
#endif
                for (typename TR::addressingMode<THword>::iterator off_it = am.begin();
                    off_it.check();
                    off_it.next()) {
                    count++;
                    THword offset = *off_it;
                    THword raddr = am.getBase() + offset;
                    auto oData = load<(IRType)nbits>(raddr);
                    auto rData = ite(subval<wide>(am.getoffset()) == offset, subval<nbits>(m_ctx, data), oData.tos());
                    store(raddr, rData);
                }
            }
            else {
                Itaddress it = this->addr_begin(m_solver, address);
                while (it.check()) {
                    count++;
                    rsval<THword> addr = *it;
                    auto oData = load<(IRType)nbits>(addr);
                    auto rData = ite(subval<wide>(m_ctx, address) == addr.tos(), subval<nbits>(m_ctx, data), oData.tos());
                    store(addr, rData);
                    it++;
                }
            }
            if (!count) { throw Expt::SolverNoSolution("store error", m_solver); };
        }


        template<bool sign, int nbits, TASSERT(nbits <= 64)>
        inline void store(THword address, const sv::ctype_val<sign, nbits, Z3_BV_SORT>& data) {
            store(address, data.value());
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(THword address, const sv::symbolic<sign, nbits, Z3_BV_SORT>& data) {
            store<nbits>(address, (Z3_ast)data);
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(THword address, const sv::rsval<sign, nbits, Z3_BV_SORT>& data) {
            if (data.real()) {
                store(address, data.tor());
            }
            else {
                store<nbits>(address, (Z3_ast)data.tos());
            }
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(Z3_ast address, const sv::rsval<sign, nbits, Z3_BV_SORT>& data) {
            if (data.real()) {
                store(address, data.tor().value());
            }
            else {
                store<nbits>(address, (Z3_ast)data.tos());
            }
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(const sv::rsval<false, wide, Z3_BV_SORT>& address, const sv::rsval<sign, nbits, Z3_BV_SORT>& data) {
            if (address.real()) {
                store((THword)address.tor(), data);
            }
            else {
                store((Z3_ast)address.tos(), data);
            }
        }


        template<typename DataTy, TASSERT(std::is_arithmetic<DataTy>::value || sv::is_sse<DataTy>::value)>
        inline void store(const sv::rsval<false, wide, Z3_BV_SORT>& address, DataTy data) {
            if (address.real()) {
                store((THword)address.tor(), data);
            }
            else {
                store((Z3_ast)address.tos(), data);
            }
        }

        template<bool sign, int nbits, TASSERT((nbits & 0x7) == 0)>
        inline void store(const sv::rsval<false, wide, Z3_BV_SORT>& address, const sv::symbolic<sign, nbits, Z3_BV_SORT>& data) {
            if (address.real()) {
                store<nbits>((THword)address.tor(), (Z3_ast)data);
            }
            else {
                store<nbits>((Z3_ast)address.tos(), (Z3_ast)data);
            }
        }

        inline void Ist_Store(tval const& address, tval const& data) {
            if (address.real()) {
                Ist_Store((THword)address.tor<false, wide>(), data);
            }
            else {
                Ist_Store((Z3_ast)address.tos<false, wide>(), data);
            }
        }

        void Ist_Store(THword address, tval const& data);
        void Ist_Store(Z3_ast address, tval const& data);
    public:
        inline operator Z3_context() const { return m_ctx; };
        inline operator z3::vcontext& () { return m_ctx; };
        inline z3::vcontext& ctx() { return m_ctx; };
        ;;
    private:

    };
};

#ifndef UNDEFMEM
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

#endif //  MEMORY_DEFS_H
