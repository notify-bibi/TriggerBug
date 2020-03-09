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

#include "engine/engine.hpp"
#include "engine/Variable.hpp"
#include "engine/Register.hpp"
#include "engine/State_class.hpp"

extern UInt global_user;
extern std::mutex global_user_mutex;


#define fastMaskI1(n) fastMask(((n)+1))
#define fastMaskReverseI1(N) (~fastMaskI1(N))

#define LZDEF(n) ((unsigned char)(((((((int)(n))-1) & -8) + 8) >> 3) - 1))
const UChar fastalignD1[257] = { LZDEF(0),  LZDEF(1),  LZDEF(2),  LZDEF(3),  LZDEF(4),  LZDEF(5),  LZDEF(6),  LZDEF(7),  LZDEF(8),  LZDEF(9),  LZDEF(10),  LZDEF(11),  LZDEF(12),  LZDEF(13),  LZDEF(14),  LZDEF(15),  LZDEF(16),  LZDEF(17),  LZDEF(18),  LZDEF(19),  LZDEF(20),  LZDEF(21),  LZDEF(22),  LZDEF(23),  LZDEF(24),  LZDEF(25),  LZDEF(26),  LZDEF(27),  LZDEF(28),  LZDEF(29),  LZDEF(30),  LZDEF(31),  LZDEF(32),  LZDEF(33),  LZDEF(34),  LZDEF(35),  LZDEF(36),  LZDEF(37),  LZDEF(38),  LZDEF(39),  LZDEF(40),  LZDEF(41),  LZDEF(42),  LZDEF(43),  LZDEF(44),  LZDEF(45),  LZDEF(46),  LZDEF(47),  LZDEF(48),  LZDEF(49),  LZDEF(50),  LZDEF(51),  LZDEF(52),  LZDEF(53),  LZDEF(54),  LZDEF(55),  LZDEF(56),  LZDEF(57),  LZDEF(58),  LZDEF(59),  LZDEF(60),  LZDEF(61),  LZDEF(62),  LZDEF(63),  LZDEF(64),  LZDEF(65),  LZDEF(66),  LZDEF(67),  LZDEF(68),  LZDEF(69),  LZDEF(70),  LZDEF(71),  LZDEF(72),  LZDEF(73),  LZDEF(74),  LZDEF(75),  LZDEF(76),  LZDEF(77),  LZDEF(78),  LZDEF(79),  LZDEF(80),  LZDEF(81),  LZDEF(82),  LZDEF(83),  LZDEF(84),  LZDEF(85),  LZDEF(86),  LZDEF(87),  LZDEF(88),  LZDEF(89),  LZDEF(90),  LZDEF(91),  LZDEF(92),  LZDEF(93),  LZDEF(94),  LZDEF(95),  LZDEF(96),  LZDEF(97),  LZDEF(98),  LZDEF(99),  LZDEF(100),  LZDEF(101),  LZDEF(102),  LZDEF(103),  LZDEF(104),  LZDEF(105),  LZDEF(106),  LZDEF(107),  LZDEF(108),  LZDEF(109),  LZDEF(110),  LZDEF(111),  LZDEF(112),  LZDEF(113),  LZDEF(114),  LZDEF(115),  LZDEF(116),  LZDEF(117),  LZDEF(118),  LZDEF(119),  LZDEF(120),  LZDEF(121),  LZDEF(122),  LZDEF(123),  LZDEF(124),  LZDEF(125),  LZDEF(126),  LZDEF(127),  LZDEF(128),  LZDEF(129),  LZDEF(130),  LZDEF(131),  LZDEF(132),  LZDEF(133),  LZDEF(134),  LZDEF(135),  LZDEF(136),  LZDEF(137),  LZDEF(138),  LZDEF(139),  LZDEF(140),  LZDEF(141),  LZDEF(142),  LZDEF(143),  LZDEF(144),  LZDEF(145),  LZDEF(146),  LZDEF(147),  LZDEF(148),  LZDEF(149),  LZDEF(150),  LZDEF(151),  LZDEF(152),  LZDEF(153),  LZDEF(154),  LZDEF(155),  LZDEF(156),  LZDEF(157),  LZDEF(158),  LZDEF(159),  LZDEF(160),  LZDEF(161),  LZDEF(162),  LZDEF(163),  LZDEF(164),  LZDEF(165),  LZDEF(166),  LZDEF(167),  LZDEF(168),  LZDEF(169),  LZDEF(170),  LZDEF(171),  LZDEF(172),  LZDEF(173),  LZDEF(174),  LZDEF(175),  LZDEF(176),  LZDEF(177),  LZDEF(178),  LZDEF(179),  LZDEF(180),  LZDEF(181),  LZDEF(182),  LZDEF(183),  LZDEF(184),  LZDEF(185),  LZDEF(186),  LZDEF(187),  LZDEF(188),  LZDEF(189),  LZDEF(190),  LZDEF(191),  LZDEF(192),  LZDEF(193),  LZDEF(194),  LZDEF(195),  LZDEF(196),  LZDEF(197),  LZDEF(198),  LZDEF(199),  LZDEF(200),  LZDEF(201),  LZDEF(202),  LZDEF(203),  LZDEF(204),  LZDEF(205),  LZDEF(206),  LZDEF(207),  LZDEF(208),  LZDEF(209),  LZDEF(210),  LZDEF(211),  LZDEF(212),  LZDEF(213),  LZDEF(214),  LZDEF(215),  LZDEF(216),  LZDEF(217),  LZDEF(218),  LZDEF(219),  LZDEF(220),  LZDEF(221),  LZDEF(222),  LZDEF(223),  LZDEF(224),  LZDEF(225),  LZDEF(226),  LZDEF(227),  LZDEF(228),  LZDEF(229),  LZDEF(230),  LZDEF(231),  LZDEF(232),  LZDEF(233),  LZDEF(234),  LZDEF(235),  LZDEF(236),  LZDEF(237),  LZDEF(238),  LZDEF(239),  LZDEF(240),  LZDEF(241),  LZDEF(242),  LZDEF(243),  LZDEF(244),  LZDEF(245),  LZDEF(246),  LZDEF(247),  LZDEF(248),  LZDEF(249),  LZDEF(250),  LZDEF(251),  LZDEF(252),  LZDEF(253),  LZDEF(254),  LZDEF(255),  LZDEF(256) };
#undef  LZDEF



#ifdef _DEBUG
#define NEED_VERIFY 
#define TRACE_AM
#endif

#define BIT_BLAST_MAX_BIT 14
#define ANALYZER_TIMEOUT 0.4d

#define LINETOSTR(A) #A
#define CONCATSTR(A, B) " ACCESS MEM ERR UNMAPPED; " A " AT Line: " LINETOSTR(B)

//客户机内存访问检查
#define MEM_ACCESS_ASSERT_R(CODE, ADDRESS) if (!(CODE)) throw Expt::GuestMemReadErr(CONCATSTR(__FILE__, __LINE__), ADDRESS);
#define MEM_ACCESS_ASSERT_W(CODE, ADDRESS) if (!(CODE)) throw Expt::GuestMemWriteErr(CONCATSTR(__FILE__, __LINE__), ADDRESS);

//检查是否将ir translate的block区代码修改了，避免某些vmp或者ctf的恶作剧
#define CODEBLOCKISWRITECHECK(address) if(m_ee) m_ee->block_integrity(address);

template<typename ADDR>
class addressingMode
{
public:
    enum addressingModeKind {
        cant_analysis = 0,
        found_base_and_offset,
        support_bit_blast
    };

private:
    struct sbit_struct {
        Z3_ast sym_ast;
        bool rbit;
        UInt idx;
    };

    struct sbit_struct_r {
        sbit_struct sbit;
        ADDR sign_mask;
        UInt nbit;
    };

    //超集的解遍历算法
    template<typename ADDR>
    class iterator
    {
        struct shift_mask {
            UChar shift;
            ADDR mask;
        };

    private:
        ADDR m_sym_mask;
        ADDR m_or_mask;
        ADDR tmp_bit_blast;
        ADDR tmp_target_bit_blast;
        struct shift_mask m_sym_ml[BIT_BLAST_MAX_BIT];
        UInt m_sym_ml_n;


        struct shift_mask m_sign_ml[32];
        UInt m_sign_ml_n;

    public:
        inline iterator() {};

        inline iterator(addressingMode<ADDR>&am) :
            m_sym_mask(am.m_sym_mask),
            m_or_mask(am.m_or_mask),
            tmp_bit_blast((ADDR)0),
            tmp_target_bit_blast((ADDR)0),
            m_sym_ml_n(0),
            m_sign_ml_n(0)
        {
            DWORD N;
            UInt _pcur;
            UInt nb = 0;

            if (_BitScanForward64(&N, m_sym_mask)) {
                m_sym_ml[0] = shift_mask{(UChar)N,((ADDR)1) << N };
                m_sym_ml_n = 1;
                _pcur = N;
                tmp_target_bit_blast = ((ADDR)1);
                nb = 1;

                for (; ; ) {
                    if (_BitScanForward64(&N, m_sym_mask & fastMaskReverseI1(_pcur))) {
                        if (N = _pcur + 1) {
                            m_sym_ml[m_sym_ml_n - 1].mask |= ((ADDR)1) << N;
                        }
                        else {
                            m_sym_ml[m_sym_ml_n - 1] = shift_mask{ (UChar)N,((ADDR)1) << N };
                            m_sym_ml_n++;
                        }
                        tmp_target_bit_blast |= ((ADDR)1) << (nb++);
                        _pcur = N;
                    }
                    else {
                        break;
                    }
                }
            }

        parse_sign:
            for (auto s : am.m_sign_mask) {
                m_sign_ml[m_sign_ml_n++] = shift_mask{ (UChar)nb, s };
                tmp_target_bit_blast |= ((ADDR)1) << (nb++);
            }
            tmp_target_bit_blast += 1;
        }


        inline bool operator!=(const iterator& src)
        {
            return tmp_bit_blast != tmp_target_bit_blast;
        }

        inline void operator++()
        {
            tmp_bit_blast++;
        }

        inline ADDR operator*()
        {
            ADDR re = 0;
            for (UInt sign_ml_n = 0; sign_ml_n < m_sign_ml_n; sign_ml_n++) {
                if ((tmp_bit_blast >> m_sign_ml[sign_ml_n].shift) & 1) {
                    re |= m_sign_ml[sign_ml_n].mask;
                }
            }
            for (UInt sym_ml_n = 0; sym_ml_n < m_sym_ml_n; sym_ml_n++) {
                re |= (tmp_bit_blast << m_sym_ml[sym_ml_n].shift) & m_sym_ml[sym_ml_n].mask;
            }
            return re | m_or_mask;
        }
    };



private:
    z3::context& m_ctx;
    z3::expr m_symbolic;
    ADDR m_base;
    z3::expr m_offset;

    std::vector<ADDR> m_sign_mask;
    ADDR m_sym_mask;
    UInt m_sym_mask_n;
    ADDR m_or_mask;

    addressingModeKind m_analysis_kind;
public:
    addressingMode(const z3::expr& e) :
        m_ctx(e.ctx()),
        m_symbolic(e),
        m_sym_mask(0ull),
        m_or_mask(0ull),
        m_sym_mask_n(0),
        m_offset(m_ctx)
    {
        if (ast2baseAoffset()) {
            if (offset_bit_blast()) {
                m_analysis_kind = support_bit_blast;
            }
            else {
                m_analysis_kind = found_base_and_offset;
            }
        }
        else {
            m_analysis_kind = cant_analysis;
        }
    }

    void offset2opAdd(std::vector<Vns>& ret) {
        _offset2opAdd(ret, m_offset);
    }

private:
    // ast(symbolic address) = numreal(base) + symbolic(offset) 
    bool ast2baseAoffset() {
        //std::cout << saddr.simplify() << std::endl << std::endl;
        z3::expr base = z3::expr(m_ctx);
        m_offset = _ast2base(base, m_symbolic, 0, 6);
        //std::cout << idx << std::endl;
        ULong _m_base;
        if ((Z3_ast)base) {
            if (base.simplify().is_numeral_u64(_m_base)) {
                m_base = _m_base;
#if defined(NEED_VERIFY)
                if (m_base > 100) {
                    Int is_right;
                    z3::expr eval = base + m_offset == m_symbolic;
                    if (z3::ite(eval, m_ctx.bv_val(1, 8), m_ctx.bv_val(0, 8)).simplify().is_numeral_i(is_right)) {
                        if (is_right) {
                            return true;
                        }
                        else {
                            goto faild;
                        }
                    }
                    else {
                        vex_printf("cant determine base %p try solver:\n", m_base);
                    }
                    z3::solver s(m_ctx);
                    s.add(!eval);
                    if (s.check() == z3::unsat) {
                        return true;
                    }
                    std::cout << "unsat model:\n" << s.get_model() << std::endl;
                    goto faild;
                }
#else
                return true;
#endif
                }
        }
        return false;
faild:
        std::cout << "symbolic:\n" << m_symbolic << std::endl << std::endl;
        std::cout << "symbolic.simplify:\n" << m_symbolic.simplify() << std::endl << std::endl;

        std::cout << "base:\n" << m_base << std::endl << std::endl;
        std::cout << "Index:\n" << m_offset << std::endl << std::endl;

        vex_printf("is False  %p\n", m_base);
        vpanic("sorry .engine error.  report me and i will fix it\n");
    }

    //分析offset 使分析器能够求解出超集
    bool offset_bit_blast() {
        z3::sort so = m_offset.get_sort();
        UInt size = so.bv_size();

        std::vector<sbit_struct_r> vec;
        for (UInt idx = 0; idx < size; idx++) {
            sbit_struct s = _check_is_extract(m_offset, idx);
            //把ast分解为 一个一个bit独立单元
            if (s.sym_ast) {
                auto end = vec.end();
                auto m = vec.begin();
                bool exist = false;
                while (m != end) {
                    if (s.sym_ast == m->sbit.sym_ast && s.idx == m->sbit.idx) {
                        m->sign_mask |= ((ADDR)1) << idx;
                        m->nbit++;
                        exist = true;
                        break;
                    }
                    m++;
                };
                if (!exist) {
                    vec.emplace_back(sbit_struct_r{ s  , ((ADDR)1) << idx, 1 });
                };
            }
            else {
                m_or_mask = m_or_mask | ((ADDR)s.rbit << idx);
            }
        }

        
        auto end = vec.end();
        auto m = vec.begin();
        while (m != end) {
            if (m->nbit == 1) {
                m_sym_mask |= m->sign_mask;
                m_sym_mask_n++;
            }
            else {
                m_sign_mask.emplace_back(m->sign_mask);
            }
            m++;
        }
        return ((m_sym_mask_n + m_sign_mask.size()) >= BIT_BLAST_MAX_BIT) ? false : true;
    }

public:
    addressingModeKind analysis_kind() {
        return m_analysis_kind;
    }


    inline ADDR getBase() {
        assert(m_analysis_kind != cant_analysis);
        return m_base;
    }

    inline z3::expr getoffset() {
        assert(m_analysis_kind != cant_analysis);
        return m_offset;
    }

    inline addressingMode(const addressingMode<ADDR>& a) :
        m_ctx(a.m_ctx),
        m_offset(a.m_offset),
        m_base(a.m_base),
        m_symbolic(a.m_symbolic)
    {

    }

    inline void operator=(const addressingMode<ADDR>& a)
    {
        this->~addressingMode();
        m_offset = a.m_offset;
        m_base = a.m_base;
        m_symbolic = a.m_symbolic;
    }

    inline ~addressingMode() {
    }


    inline iterator<ADDR> begin() {
        assert(m_analysis_kind == support_bit_blast);
        return iterator<ADDR>(*this);
    }

    inline iterator<ADDR> end() {
        return iterator<ADDR>();
    }

    void print() {
        printf("\tor_mask: %016x\t\t", m_or_mask);
        printf("sym_mask: n:%d %016x\n", m_sym_mask_n, m_sym_mask);
        if (!m_sign_mask.empty()) {
            printf("sign_mask: \n\t{\n", m_or_mask);
            for (auto sm : m_sign_mask) {
                printf("\t\t %016x\n", sm);
            }
            printf("\n\t}\n", m_or_mask);
        }
    }

    void print_offset() {
        std::cout << m_offset << std::endl;
    }
private:
    static z3::expr _ast2base(z3::expr& base,
        z3::expr const& e,
        UInt deep, UInt max_deep
    );

    static sbit_struct _check_is_extract(z3::expr const& e, UInt idx);
    //a=b+c+d+e...+z -> b c d e
    static void _offset2opAdd(std::vector<Vns>& ret, z3::expr const&e);
    static bool _check_add_no_overflow(z3::expr const& e1, z3::expr const& e2);
};

#define GETPT(address) ((*CR3)->pt[(address) >> 39 & 0x1ff]->pt[(address) >> 30 & 0x1ff]->pt[(address) >> 21 & 0x1ff])
#define GETPAGE(address) ((*CR3)->pt[(address) >> 39 & 0x1ff]->pt[(address) >> 30 & 0x1ff]->pt[(address) >> 21 & 0x1ff]->pt[(address) >> 12 & 0x1ff])
#define COPY_SYM(new_page, p_page,index) (new_page)->unit[(index)] = (p_page)->unit[(index)]


#define LCODEDEF1(PML4T_max,PML4T_ind,pdpt,PDPT_max,PDT,EXPRESS)															\
	if ((EXPRESS)) {																										\
			(*(pdpt))->pt = (PDT**)malloc(((PDPT_max) + 1) * sizeof(void *));												\
			memset((*(pdpt))->pt , 0, (PDPT_max + 1) * sizeof(void *));														\
			(*(pdpt))->size = (PDPT_max)+1;																					\
	}else {																													\
		(*(pdpt))->pt = (PDT**)malloc( 0x200 * sizeof(void *));																\
		memset((*(pdpt))->pt, 0, 0x200 * sizeof(void *));																	\
		(*(pdpt))->size = 0x200;																							\
	}

#define LCODEDEF2(PML4T_max, PML4T_ind, pdpt, PDPT_max, PDPT_ind, CR3 ,PDPT , PDT, EXPRESS)									\
	PDPT **pdpt = (*CR3)->pt + PML4T_ind;																					\
	if (!*pdpt) {																											\
		*pdpt = new PDPT;																									\
		if (!*pdpt)																											\
			goto _returnaddr;																								\
		memset(*pdpt, 0, sizeof(PDPT));																						\
		LCODEDEF1(PML4T_max,PML4T_ind,pdpt,PDPT_max,PDT,EXPRESS)															\
		(*CR3)->used += 1;																									\
		PDPT *orignal = (*CR3)->top;																						\
		(*CR3)->top = *pdpt;																								\
		(*pdpt)->prev = NULL;																								\
		(*pdpt)->next = orignal;																							\
		(*pdpt)->index = PML4T_ind;																							\
		if (orignal) orignal->prev = *pdpt;																					\
	}																														\
	else if ((*pdpt)->size <= PDPT_ind) {																					\
		if (PML4T_max == PML4T_ind) {																						\
			(*pdpt)->pt = (PDT**)realloc((*pdpt)->pt, (PDPT_ind + 1) * sizeof(void *));										\
			memset((*pdpt)->pt + (*pdpt)->size, 0, (PDPT_ind + 1 - (*pdpt)->size) * sizeof(void *));						\
			(*pdpt)->size = PDPT_ind + 1;																					\
		}																													\
		else {																												\
			(*pdpt)->pt = (PDT**)realloc((*pdpt)->pt,0x200*sizeof(void *));													\
			memset((*pdpt)->pt + (*pdpt)->size, 0, (0x200 - (*pdpt)->size) * sizeof(void *));								\
			(*pdpt)->size = 0x200;																							\
		}																													\
	}

#define LCODEDEF3(page,PT,pt)																								\
delete *page;																												\
*page = 0;																													\
(*pt)->used -= 1;																											\
if ((*pt)->used) {																											\
	address += 0x1000;																										\
	continue;																												\
}																															\
{																															\
	PT *p = (*pt)->prev;																									\
	PT *n = (*pt)->next;																									\
	if (p) p->next = n;																										\
	if (n) n->prev = p;																										\
}																														  

#define LCODEDEF4(PDPT,pdpt_point,CR3_point,lCR3,pdpt,i1)																	\
PDPT *pdpt_point = CR3_point->top;																							\
for (UInt i1 = 0; i1 < CR3_point->used; i1++, pdpt_point = pdpt_point->next) {												\
	PDPT *pdpt = new PDPT;																									\
	memset(pdpt, 0, sizeof(PDPT));																							\
	if (!lCR3->pt) {																										\
		lCR3->pt = (PDPT**)malloc(CR3_point->size * 8);																		\
		memset(lCR3->pt,0,CR3_point->size * 8);																				\
	}																														\
	lCR3->pt[pdpt_point->index] = pdpt;																						\
	{																														\
		PDPT *orignal = lCR3->top;																							\
		lCR3->top = pdpt;																									\
		(pdpt)->prev = NULL;																								\
		(pdpt)->next = orignal;																								\
		(pdpt)->index = pdpt_point->index;																					\
		if (orignal) orignal->prev = pdpt;																					\
	}																														\


#define LCODEDEF5(PDPT,pdpt_point,free_pdpt_point,CR3_point,i1,codenext)													\
PDPT *pdpt_point = CR3_point->top;																							\
for (UInt i1 = 0; i1 < CR3_point->used; i1++) {																				\
	codenext																												\
	free(pdpt_point->pt);																									\
	auto free_pdpt_point = pdpt_point;																						\
	pdpt_point = pdpt_point->next;																							\
	delete free_pdpt_point;																									\
}                                                                                                                           \



#define LMAX1 PML4T_max
#define LMAX2 PDPT_max
#define LMAX3 PDT_max
#define LMAX4 PT_max
#define LMAX5 PAGE_max

#define LIND1 PML4T_ind
#define LIND2 PDPT_ind
#define LIND3 PDT_ind
#define LIND4 PT_ind

#define LTAB1 CR3
#define LTAB2 pdpt
#define LTAB3 pdt
#define LTAB4 pt
#define LTAB5 page

#define LSTRUCT1 PML4T
#define LSTRUCT2 PDPT
#define LSTRUCT3 PDT
#define LSTRUCT4 PT
#define LSTRUCT5 ST


namespace TRMem {
    template<class ST>
    class mapping {
    public:
        typedef struct PAGE_link {
            UShort index;
            PAGE_link* prev;
            PAGE_link* next;
        }PAGE_link;

        typedef struct PT {
            UShort used;
            UShort index;
            PAGE_link* top;
            PT* prev;
            PT* next;
            UInt size;
            ST** pt;
        }PT;

        typedef struct PDT {
            UShort used;
            UShort index;
            PT* top;
            PDT* prev;
            PDT* next;
            UInt size;
            PT** pt;
        }PDT;

        typedef struct PDPT {
            UShort used;
            UShort index;
            PDT* top;
            PDPT* prev;
            PDPT* next;
            UInt size;
            PDT** pt;
        }PDPT;

        typedef struct PML4T {
            UShort used;
            PDPT* top;
            UInt size;
            PDPT** pt;
        }PML4T;

    private:
        PML4T _CR3_;

        virtual ST* map_interface(ULong address) { vassert(0); };
        virtual void copy_interface(ST* pt_dst[1], ST* pt_src[1]) { vassert(0); };
        virtual void unmap_interface(ST* pt[1]) { vassert(0); };
        
    public:
        PML4T* CR3[1];
        mapping() {
            CR3[0] = &_CR3_;
            memset(&_CR3_, 0, sizeof(PML4T));
        }

        //客户机的分配空间算法 类似cpu的硬件虚拟映射技术。这里我们使用软件虚拟映射
        ULong map(ULong address, ULong length) {
            ULong max = (address + length - 1) & (~0xfff);
            UShort PML4T_max = (max >> 39 & 0x1ff);
            UShort PDPT_max = (max >> 30 & 0x1ff);
            UShort PDT_max = (max >> 21 & 0x1ff);
            UShort PT_max = (max >> 12 & 0x1ff);
            address &= (~0xfff);
            while (address <= max) {
                UShort PML4T_ind = (address >> 39 & 0x1ff);
                UShort PDPT_ind = (address >> 30 & 0x1ff);
                UShort PDT_ind = (address >> 21 & 0x1ff);
                UShort PT_ind = (address >> 12 & 0x1ff);
                if (!(*CR3)->pt) {
                    (*CR3)->pt = (PDPT**)malloc((PML4T_max + 1) * 8);
                    memset((*CR3)->pt, 0, (PML4T_max + 1) * sizeof(void*));
                    (*CR3)->size = PML4T_max + 1;
                }
                else {
                    if ((*CR3)->size <= PML4T_max) {
                        (*CR3)->pt = (PDPT**)realloc((*CR3)->pt, (PML4T_ind + 1) * sizeof(void*));
                        memset((*CR3)->pt + (*CR3)->size, 0, (PML4T_ind + 1 - (*CR3)->size) * sizeof(void*));
                        (*CR3)->size = PML4T_ind + 1;
                    }
                }

                LCODEDEF2(LMAX1, LIND1, LTAB2, LMAX2, LIND2, LTAB1, LSTRUCT2, LSTRUCT3, (LMAX1) == (LIND1));
                LCODEDEF2(LMAX2, LIND2, LTAB3, LMAX3, LIND3, LTAB2, LSTRUCT3, LSTRUCT4, (LMAX1) == (LIND1) && (LMAX2) == (LIND2));
                LCODEDEF2(LMAX3, LIND3, LTAB4, LMAX4, LIND4, LTAB3, LSTRUCT4, LSTRUCT5, (LMAX1) == (LIND1) && (LMAX2) == (LIND2) && (LMAX3) == (LIND3));
                /* debug LCODEDEF2(LMAX1, LIND1, .... )
                PT **pt = (*pdt)->pt + PDT_ind;
                if (!*pt) {
                    *pt = new PT;
                    if (!*pt) goto _returnaddr; memset(*pt, 0, sizeof(PT));
                    if (((PML4T_max) == (PML4T_ind) && (PDPT_max) == (PDPT_ind) && (PDT_max) == (PDT_ind))) {
                        (*(pt))->pt = (PAGE**)malloc(((PT_max)+1) * sizeof(void *)); memset((*(pt))->pt, 0, (PT_max + 1) * sizeof(void *)); (*(pt))->size = (PT_max)+1;
                    } else {
                        (*(pt))->pt = (PAGE**)malloc(0x200 * sizeof(void *)); memset((*(pt))->pt, 0, 0x200 * sizeof(void *)); (*(pt))->size = 0x200;
                    }
                    (*pdt)->used += 1;
                    PT *orignal = (*pdt)->top;
                    (*pdt)->top = *pt; (*pt)->prev = 0;
                    (*pt)->next = orignal;
                    (*pt)->index = PDT_ind;
                    if (orignal) orignal->prev = *pt;
                }
                else if ((*pt)->size <= PDPT_ind) {
                    if (PDT_max == PDT_ind) {
                        (*pt)->pt = (PAGE**)realloc((*pt)->pt, (PDPT_ind + 1) * sizeof(void *));
                        memset((*pt)->pt + (*pt)->size, 0, (PDPT_ind + 1 - (*pt)->size) * sizeof(void *));
                        (*pt)->size = PDPT_ind + 1;
                    } else {
                        (*pt)->pt = (PAGE**)realloc((*pt)->pt, 0x200 * sizeof(void *));
                        memset((*pt)->pt + (*pt)->size, 0, (0x200 - (*pt)->size) * sizeof(void *)); (*pt)->size = 0x200;
                    }
                };*/

                ST** page = (*pt)->pt + PT_ind;
                if (!*page) {
                    *page = map_interface(address);
                    //Over
                    PAGE_link* page_l = new PAGE_link;
                    if (!*page)
                        goto _returnaddr;
                    (*pt)->used += 1;
                    PAGE_link* orignal = (*pt)->top;
                    (*pt)->top = page_l;
                    (page_l)->prev = NULL;
                    (page_l)->next = orignal;
                    (page_l)->index = PT_ind;
                    if (orignal) orignal->prev = page_l;
                }
                else {
                    //goto _returnaddr; 
                }
                address += 0x1000;
                if (address == 0) return -1ull;
            }
            return 0;
        _returnaddr:
            return max - address + 0x1000;
        }

        //类似于linux的sys_fork.写时复制.速度快
        void copy(PML4T* cr3) {
            PML4T* CR3_point = cr3;
            PML4T* lCR3 = *CR3;
            LCODEDEF4(LSTRUCT2, pdpt_point, CR3_point, lCR3, LTAB2, i1);
                LCODEDEF4(LSTRUCT3, pdt_point, pdpt_point, LTAB2, LTAB3, i2);
                    LCODEDEF4(LSTRUCT4, pt_point, pdt_point, LTAB3, LTAB4, i3);
                        PAGE_link* page_point = pt_point->top;
                        for (UInt i4 = 0; i4 < pt_point->used; i4++, page_point = page_point->next) {
                            UShort index = page_point->index;
                            PAGE_link* page_l = new PAGE_link;
                            memset(page_l, 0, sizeof(PAGE_link));
                            if (!pt->pt) {
                                pt->pt = (PAGE * *)malloc(pt_point->size * 8);
                                memset(pt->pt, 0, pt_point->size * 8);
                            }
                            copy_interface(&pt->pt[index], &pt_point->pt[index]);
                            {
                                PAGE_link* orignal = (pt)->top;
                                pt->top = page_l;
                                (page_l)->prev = NULL;
                                (page_l)->next = orignal;
                                (page_l)->index = index;
                                if (orignal) orignal->prev = page_l;
                            }
                        }
                        pt->used = pt_point->used;
                        pt->size = pt_point->size;
                    }
                    pdt->used = pdt_point->used;
                    pdt->size = pdt_point->size;
                }
                pdpt->used = pdpt_point->used;
                pdpt->size = pdpt_point->size;
            }
            lCR3->used = CR3_point->used;
            lCR3->size = CR3_point->size;
        }

        //释放物理页
        ULong unmap(ULong address, ULong length) {
            ULong max = (address + length - 1) & (~0xfff);
            address &= (~0xfff);
    #ifdef OPSTR
            int freecount = 0;
    #endif
            while (address <= max) {
                PDPT** pdpt = (*CR3)->pt + (address >> 39 & 0x1ff);
                if (!*pdpt) {
                    return address;
                }
                PDT** pdt = (*pdpt)->pt + (address >> 30 & 0x1ff);
                if (!*pdt) {
                    return address;
                }
                PT** pt = (*pdt)->pt + (address >> 21 & 0x1ff);
                if (!*pt) {
                    return address;
                }
                UShort PT_ind = (address >> 12 & 0x1ff);
                ST** page = (*pt)->pt + PT_ind;
                if (*page) {
                    PAGE_link* page_l = (*pt)->top;
                    for (UInt i = 0; i < (*pt)->used; i++, page_l = page_l->next) {
                        if ((page_l) && (page_l->index == PT_ind)) {
                            {
                                PAGE_link* p = (page_l)->prev;
                                PAGE_link* n = (page_l)->next;
                                if (p) p->next = n;
                                if (n) n->prev = p;
                            }
                            delete page_l;
    #ifdef OPSTR
                            freecount++;
    #endif
                            break;
                        }
                    }
                    unmap_interface(page);
                    // LCODEDEF3(LTAB5, LSTRUCT4, LTAB4)
                    (*pt)->used -= 1;
                    if ((*pt)->used) {
                        address += 0x1000;
                        continue;
                    }
                    {
                        PT* p = (*pt)->prev;
                        PT* n = (*pt)->next;
                        if (p) p->next = n;
                        if (n) n->prev = p;
                    }
                    free((*pt)->pt);
                    LCODEDEF3(LTAB4, LSTRUCT3, LTAB3)
                        free((*pdt)->pt);
                    LCODEDEF3(LTAB3, LSTRUCT2, LTAB2)
                        free((*pdpt)->pt);
                    delete* pdpt;
                    *pdpt = 0;
                    (*CR3)->used -= 1;
                    address += 0x1000;
                }
                else {
                    return address;
                }
            }
    #ifdef OPSTR
            vex_printf("free count %x\n", freecount);
    #endif
            return 0;
        }
        
        void recycle() {
            if (!CR3[0]) return;
            PML4T* CR3_point = CR3[0];
            //  遍历双向链表
            LCODEDEF5(LSTRUCT2, pdpt_point, free_pdpt_point, CR3_point, i1,
                LCODEDEF5(LSTRUCT3, pdt_point, free_pdt_point, pdpt_point, i2,
                    LCODEDEF5(LSTRUCT4, pt_point, free_pt_point, pdt_point, i3,
                        PAGE_link * page_point = pt_point->top;
                        for (UInt i4 = 0; i4 < pt_point->used; i4++) {
                            UShort index = page_point->index;
                            unmap_interface(&pt_point->pt[index]);
                            auto free_page_point = page_point;
                            page_point = page_point->next;
                            delete free_page_point;
                        }
                    )
                )
            )
            CR3[0] = nullptr;
        }

        ~mapping() { vassert(!CR3[0]); }

        //虚拟映射一个虚拟地址
        inline ST** get_pointer_of_mem_page(Addr64 address) {
            UShort PML4T_ind = (address >> 39 & 0x1ff);
            UShort PDPT_ind = (address >> 30 & 0x1ff);
            UShort PDT_ind = (address >> 21 & 0x1ff);
            UShort PT_ind = (address >> 12 & 0x1ff);
            if (PML4T_ind < (*CR3)->size) {
                PDPT* pdpt = (*CR3)->pt[PML4T_ind];
                if (pdpt && PDPT_ind < pdpt->size) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    if (pdt && PDT_ind < pdt->size) {
                        PT* pt = pdt->pt[PDT_ind];
                        if (pt && PT_ind < pt->size) {
                            return &pt->pt[PT_ind];
                        }
                    }
                }
            }
            return nullptr;
        };

        inline ST** get_pointer_of_mem_page(Addr32 address) {
            UShort PDPT_ind = (address >> 30 & 0x3);
            UShort PDT_ind = (address >> 21 & 0x1ff);
            UShort PT_ind = (address >> 12 & 0x1ff);
            if ((*CR3)->size) {
                PDPT* pdpt = (*CR3)->pt[0];
                if (pdpt && PDPT_ind < pdpt->size) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    if (pdt && PDT_ind < pdt->size) {
                        PT* pt = pdt->pt[PDT_ind];
                        if (pt && PT_ind < pt->size) {
                            return &pt->pt[PT_ind];
                        }
                    }
                }
            }
            return nullptr;
        };

        inline ST* getMemPage(Addr32 address) {
            ST** r = get_pointer_of_mem_page(address);
            return (r) ? r[0] : nullptr;
        }

        inline ST* getMemPage(Addr64 address) {
            ST** r = get_pointer_of_mem_page(address);
            return (r) ? r[0] : nullptr;
        }

        //find block reverse;
        inline ST** find_mem_page_reverse(Addr64 address, Addr64 &ret) {
            Int PML4T_ind = (address >> 39 & 0x1ff);
            Int PDPT_ind = (address >> 30 & 0x1ff);
            Int PDT_ind = (address >> 21 & 0x1ff);
            Int PT_ind = (address >> 12 & 0x1ff);
            for (; PML4T_ind >= 0; PML4T_ind--) {
                PDPT* pdpt = (*CR3)->pt[PML4T_ind];
                for (; pdpt && PDPT_ind >= 0; PDPT_ind--) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    for (; pdt && PDT_ind >= 0; PDT_ind--) {
                        PT* pt = pdt->pt[PDT_ind];
                        for (; pt && PT_ind >= 0; PT_ind--) {
                            if (pt->pt[PT_ind]) {
                                ret = (((Addr64)PML4T_ind) << 39) | (((Addr64)PDPT_ind) << 30) | (((Addr64)PDT_ind) << 21) | (((Addr64)PT_ind) << 12);
                                return &pt->pt[PT_ind];
                            }
                        }
                    }
                }
            }
            return nullptr;
        };

        //find block reverse;
        inline ST** find_mem_page_reverse(Addr32 address, Addr32& ret) {
            Int PDPT_ind = (address >> 30 & 0x1ff);
            Int PDT_ind = (address >> 21 & 0x1ff);
            Int PT_ind = (address >> 12 & 0x1ff);
            if ((*CR3)->size) {
                PDPT* pdpt = (*CR3)->pt[0];
                for (; pdpt && PDPT_ind >= 0; PDPT_ind--) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    for (; pdt && PDT_ind >= 0; PDT_ind--) {
                        PT* pt = pdt->pt[PDT_ind];
                        for (; pt && PT_ind >= 0; PT_ind--) {
                            if (pt->pt[PT_ind]) {
                                ret = (((Addr32)PDPT_ind) << 30) | (((Addr32)PDT_ind) << 21) | (((Addr32)PT_ind) << 12);
                                return &pt->pt[PT_ind];
                            }
                        }
                    }
                }
            }
            return nullptr;
        };


        //find block forward;
        inline ST** find_mem_page_forward(Addr32 address, Addr32& ret) {
            UInt PDPT_ind = (address >> 30 & 0x1ff);
            UInt PDT_ind = (address >> 21 & 0x1ff);
            UInt PT_ind = (address >> 12 & 0x1ff);
            if((*CR3)->size) {
                PDPT* pdpt = (*CR3)->pt[0];
                for (; pdpt && PDPT_ind < pdpt->size; PDPT_ind++) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    for (; pdt && PDT_ind < pdt->size; PDT_ind++) {
                        PT* pt = pdt->pt[PDT_ind];
                        for (; pt && PT_ind < pt->size; PT_ind++) {
                            if (pt->pt[PT_ind]) {
                                ret = (((Addr32)PDPT_ind) << 30) | (((Addr32)PDT_ind) << 21) | (((Addr32)PT_ind) << 12);
                                return &pt->pt[PT_ind];
                            }
                        }
                    }
                }
            }
            return nullptr;
        };

        inline ST** find_mem_page_forward(Addr64 address, Addr64& ret) {
            UInt PML4T_ind = (address >> 39 & 0x1ff);
            UInt PDPT_ind = (address >> 30 & 0x1ff);
            UInt PDT_ind = (address >> 21 & 0x1ff);
            UInt PT_ind = (address >> 12 & 0x1ff);
            for (; PML4T_ind < (*CR3)->size; PML4T_ind++) {
                PDPT* pdpt = (*CR3)->pt[PML4T_ind];
                for (; pdpt && PDPT_ind < pdpt->size; PDPT_ind++) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    for (; pdt && PDT_ind < pdt->size; PDT_ind++) {
                        PT* pt = pdt->pt[PDT_ind];
                        for (; pt && PT_ind < pt->size; PT_ind++) {
                            if (pt->pt[PT_ind]) {
                                ret = (((Addr64)PML4T_ind) << 39) | (((Addr64)PDPT_ind) << 30) | (((Addr64)PDT_ind) << 21) | (((Addr64)PT_ind) << 12);
                                return &pt->pt[PT_ind];
                            }
                        }
                    }
                }
            }
            return nullptr;
        };
    };

};



using namespace TRMem;

class PAGE {
    Int _m_user_;
    Int m_user;
    std::atomic_int m_ref_cound;
    UChar m_pad = 0xcc;
    UChar m_is_pad = true;
    Register<0x1000>* m_unit = nullptr;
public:
    inline bool is_pad() { return m_is_pad; };
    inline PAGE(Int u) :m_ref_cound(1), m_user(u), _m_user_(u){};
    inline Int get_user() const { return _m_user_; };
    inline UChar get_pad() const { return m_pad; };
    inline void set_pad(UChar pad) { 
        m_pad = pad; m_is_pad = true;
        vassert(!m_unit);
    };
    void copy(PAGE const* P, TRcontext& ctx, bool nr) {
        if (P->m_is_pad) {// 该页是填充区，则开始分配该页
            vassert(P->m_unit == NULL);
            m_unit = new Register<0x1000>(ctx, nr);
            memset(m_unit->m_bytes, P->m_pad, 0x1000);
        }
        else {
            m_unit = new Register<0x1000>(*(P->m_unit), ctx, nr);
        }
        m_is_pad = false;
    }
    inline void disable_pad(TRcontext& ctx, bool nr) {
        // 该页是填充区，则开始分配该页
        if (m_is_pad) {
            vassert(m_unit == NULL);
            m_unit = new Register<0x1000>(ctx, nr);
            memset(m_unit->m_bytes, m_pad, 0x1000);
            m_is_pad = false;
        }
    }
    inline void malloc_unit(TRcontext& ctx, bool nr) {
        // 该页是填充区，则开始分配该页
        if (m_is_pad) {
            vassert(m_unit == NULL);
            m_unit = new Register<0x1000>(ctx, nr);
            m_is_pad = false;
        }
    }
    inline  Register<0x1000>* operator->() { return m_unit; }
    inline  operator Register<0x1000>* () { return m_unit; }
    inline void lock(Int& xchg_user) {
        xchg_user = 0;
        while (!xchg_user) { __asm__ __volatile("xchgb %b0,%1":"=r"(xchg_user) : "m"(m_user), "0"(xchg_user) : "memory"); }
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

    ~PAGE() {
        vassert(m_ref_cound == 0); 
        if (m_unit) {
            delete m_unit;
        }
    }
};

template<typename ADDR>
class MEM : public mapping<PAGE> {
    friend class State<ADDR>; 
    template<typename ADDR>
    friend class StateMEM;
    friend class DMEM;
public:
    class Itaddress {
    private:
        z3::solver& m_solver;
        z3::context& m_ctx;
        Z3_ast m_addr;
        Z3_ast last_avoid_addr;
        UShort m_nbit;
        //std::vector<Z3_model> v_model;
    public:
        Z3_lbool m_lbool;
        inline Itaddress(z3::solver& s, Z3_ast addr) :m_ctx(m_solver.ctx()), m_solver(s), m_addr(addr), m_nbit(Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_addr))) {
            m_addr = Z3_simplify(s.ctx(), m_addr);
            Z3_inc_ref(m_ctx, m_addr);
            m_solver.push();
            Z3_ast so = Z3_mk_bvugt(m_ctx, m_addr, m_ctx.bv_val(1ull, m_nbit));
            Z3_inc_ref(m_ctx, so);
            Z3_solver_assert(m_ctx, m_solver, so);
            Z3_dec_ref(m_ctx, so);
            //v_model.reserve(20);
        }

        inline bool check() { 
            m_lbool = Z3_solver_check(m_ctx, m_solver);
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

        inline Vns operator*()
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
            return Vns(m_ctx, ret, m_nbit);
        }
        inline ~Itaddress() {
            Z3_dec_ref(m_ctx, m_addr);
            m_solver.pop();
            //for (auto m : v_model) Z3_model_dec_ref(m_ctx, m);
        }
    };
private:
    std::hash_map<ADDR, Register<0x1000>*> mem_change_map;
    Bool            need_record;
    Int             user;
    TRcontext&      m_ctx;
    z3::solver&         m_solver;
    EmuEnvironment<MAX_IRTEMP>* m_ee = nullptr;

    virtual PAGE* map_interface(ULong address) override;
    virtual void copy_interface(PAGE* pt_dst[1], PAGE* pt_src[1]) override;
    virtual void unmap_interface(PAGE* pt[1]) override;

private:
    void CheckSelf(PAGE*& P, ADDR address);
    void init_page(PAGE*& P, ADDR address);
    UInt write_bytes(ULong address, ULong length, UChar* data);
    MEM(z3::solver& s, TRcontext& ctx, PML4T** cr3, Int _user, Bool _need_record):
        m_solver(s),
        m_ctx(ctx),
        need_record(_need_record),
        user(_user)
    {
        CR3[0] = cr3[0];
    };

public:
    MEM(z3::solver& so, TRcontext& ctx, Bool _need_record);
    MEM(z3::solver& so, TRcontext& ctx, MEM& father_mem, Bool _need_record);
    ~MEM() { recycle(); }
    void set(EmuEnvironment<MAX_IRTEMP>* e) { m_ee = e; }
    virtual Z3_ast idx2Value(Addr64 base, Z3_ast idx) { return nullptr; };
    //清空写入记录
    void clearRecord();
    ULong find_block_forward(ULong start, ADDR size);
    ULong find_block_reverse(ULong start, ADDR size);
    inline std::hash_map<ADDR, Register<0x1000>*> change_map() { return mem_change_map; }
    inline Int get_user() { return user; }
    //把两个不连续的页放到Pap里，以支持valgrind的跨页翻译
    inline void set_double_page(ADDR address, Pap &addrlst) {
        addrlst.guest_addr = address;
        addrlst.Surplus = 0x1000 - (address & 0xfff);
        PAGE* P = getMemPage(address);
        MEM_ACCESS_ASSERT_R(P, address);
        addrlst.t_page_addr = (UChar*)(*P)->m_bytes + (address & 0xfff);
    }
    

    inline UChar* get_next_page(Addr32 address) {
        PAGE* P = getMemPage(address + 0x1000);
        return P ? (*P)->m_bytes : nullptr;
    }

    inline UChar* get_next_page(Addr64 address) {
        PAGE* P = getMemPage(address + 0x1000);
        return P ? (*P)->m_bytes : nullptr;
    }
    Itaddress addr_begin(z3::solver& s, Z3_ast addr) { return Itaddress(s, addr); }

    private:
        Vns _Iex_Load_a(PAGE* P, ADDR address, UShort size) {
            PAGE* nP = getMemPage(address + 0x1000);
            MEM_ACCESS_ASSERT_R(nP, address + 0x1000);
            UInt plength = 0x1000 - ((UShort)address & 0xfff);
            return (*nP)->Iex_Get(0, size - plength).translate(m_ctx).Concat((*P)->Iex_Get(((UShort)address & 0xfff), plength));
        }

        Vns _Iex_Load_b(PAGE* P, ADDR address, UShort size) {
            PAGE* nP = getMemPage(address + 0x1000);
            MEM_ACCESS_ASSERT_R(nP, address + 0x1000);
            UInt plength = 0x1000 - ((UShort)address & 0xfff);
            return (*nP)->Iex_Get(0, size - plength).translate(m_ctx).Concat((*P)->Iex_Get(((UShort)address & 0xfff), plength, m_ctx));
        }

    template<IRType ty>
    inline Vns Pad2Value(UChar pad) {
        switch (ty) {
        case 8:
        case Ity_I8:  return Vns(m_ctx, (UChar)pad);
        case 16:
        case Ity_I16: {return Vns(m_ctx, (UShort)((((UShort)pad) << 8) | pad)); }
        case 32:
        case Ity_F32:
        case Ity_I32: {return Vns(m_ctx, _mm_set1_epi8(pad).m128i_u32[0]); }
        case 64:
        case Ity_F64:
        case Ity_I64: {return Vns(m_ctx, _mm_set1_epi8(pad).m128i_u64[0]); }
        case 128:
        case Ity_I128:
        case Ity_V128: {return Vns(m_ctx,  _mm_set1_epi8(pad)); }
        case 256:
        case Ity_V256: {return Vns(m_ctx, _mm256_set1_epi8(pad)); }
        default:vpanic("error IRType");
        }
    }

    public:
    // ty  IRType || n_bits
    template<IRType ty>
    inline Vns Iex_Load(ADDR address)
    {
        PAGE *P = getMemPage(address);
        MEM_ACCESS_ASSERT_R(P, address);
        UShort offset = (UShort)address & 0xfff;
        if (P->is_pad()) {
            return Pad2Value<ty>(P->get_pad());
        };
        if (user == P->get_user()) {//WNC
            switch (ty) {
            case 8:
            case Ity_I8:  return (*P)->Iex_Get<Ity_I8>(offset);
            case 16:
            case Ity_I16: {
                if (offset >= 0xfff) { return _Iex_Load_a(P, address, 2); }return (*P)->Iex_Get<Ity_I16>(offset);
            }
            case 32:
            case Ity_F32:
            case Ity_I32: {
                if (offset >= 0xffd) { return _Iex_Load_a(P, address, 4); }return (*P)->Iex_Get<Ity_I32>(offset);
            }
            case 64:
            case Ity_F64:
            case Ity_I64: {
                if (offset >= 0xff9) { return _Iex_Load_a(P, address, 8); }return (*P)->Iex_Get<Ity_I64>(offset);
            }
            case 128:
            case Ity_I128:
            case Ity_V128: {
                if (offset >= 0xff1) { return _Iex_Load_a(P, address, 16); }return (*P)->Iex_Get<Ity_V128>(offset);
            }
            case 256:
            case Ity_V256: {
                if (offset >= 0xfe1) { return _Iex_Load_a(P, address, 32); }return (*P)->Iex_Get<Ity_V256>(offset);
            }
            default:vpanic("error IRType");
            }
        }
        else {
            switch (ty) {
            case 8:
            case Ity_I8: {
                return (*P)->Iex_Get<Ity_I8 >(offset, m_ctx);
            }
            case 16:
            case Ity_I16: {
                if (offset >= 0xfff) { return _Iex_Load_b(P, address, 2); }; return (*P)->Iex_Get<Ity_I16>(offset, m_ctx);
            }
            case 32:
            case Ity_F32:
            case Ity_I32: {
                if (offset >= 0xffd) { return _Iex_Load_b(P, address, 4); }; return (*P)->Iex_Get<Ity_I32>(offset, m_ctx);
            }
            case 64:
            case Ity_F64:
            case Ity_I64: {
                if (offset >= 0xff9) { return _Iex_Load_b(P, address, 8); }; return (*P)->Iex_Get<Ity_I64>(offset, m_ctx);
            }
            case 128:
            case Ity_I128:
            case Ity_V128: {
                if (offset >= 0xff1) { return _Iex_Load_b(P, address, 16); }; return (*P)->Iex_Get<Ity_V128>(offset, m_ctx);
            }
            case 256:
            case Ity_V256: {
                if (offset >= 0xfe1) { return _Iex_Load_b(P, address, 32); }; return (*P)->Iex_Get<Ity_V256>(offset, m_ctx);
            }
            default:vpanic("error IRType");
            }
        }
    }

    Vns Iex_Load(ADDR address, IRType ty);

    template<IRType ty>
    Vns Iex_Load(Z3_ast address) {
        addressingMode<ADDR> am(z3::expr(m_ctx, address));
        Z3_ast reast = nullptr;
        auto kind = am.analysis_kind();
        if (kind != addressingMode<ADDR>::cant_analysis) {
#ifdef TRACE_AM
            printf("Iex_Load  base: %p {\n", am.getBase());
            am.print();
            printf("}\n");
            //am.print_offset();
#endif
            reast = idx2Value(am.getBase(), am.getoffset());
            if (reast) {
                return Vns(m_ctx, reast, no_inc{});
            }
            else {
                if (kind == addressingMode<ADDR>::support_bit_blast) {
                    for (auto offset : am) {
                        Vns data = Iex_Load<ty>(am.getBase() + offset);
                        if (!reast) {
                            reast = data;
                            Z3_inc_ref(m_ctx, reast);
                            continue;
                        }
                        auto eq = Z3_mk_eq(m_ctx, am.getoffset(), Vns(m_ctx, (ADDR)offset));
                        Z3_inc_ref(m_ctx, eq);
                        auto ift = Z3_mk_ite(m_ctx, eq, data, reast);
                        Z3_inc_ref(m_ctx, ift);
                        Z3_dec_ref(m_ctx, reast);
                        Z3_dec_ref(m_ctx, eq);
                        reast = ift;
                    }
                    return Vns(m_ctx, reast, no_inc{});
                }
            }
        }
        Itaddress it = this->addr_begin(m_solver, address);
        uint64_t Z3_RE;
        while (it.check()) {
            auto addr = *it;
            if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
            Vns data = Iex_Load<ty>(Z3_RE);
            if (reast) {
                auto eq = Z3_mk_eq(m_ctx, address, addr);
                Z3_inc_ref(m_ctx, eq);
                auto ift = Z3_mk_ite(m_ctx, eq, data, reast);
                Z3_inc_ref(m_ctx, ift);
                Z3_dec_ref(m_ctx, reast);
                Z3_dec_ref(m_ctx, eq);
                reast = ift;
            }
            else {
                reast = data;
                Z3_inc_ref(m_ctx, reast);
            }
            it++;
        };
        return Vns(m_ctx, reast, no_inc{});
    }

    Vns Iex_Load(Z3_ast address, IRType ty);

    template<IRType ty>
    inline Vns Iex_Load(Vns const &address) {
        if (address.real()) {
            return Iex_Load<ty>((ADDR)address);
        }
        else {
            return Iex_Load<ty>((Z3_ast)address);
        }
    }


    inline Vns Iex_Load(Vns const &address, IRType ty)
    {
        if (address.real()) {
            return Iex_Load((ADDR)address, ty);
        }
        else {
            return Iex_Load((Z3_ast)address, ty);
        }
    }

    template<typename DataTy>
    void Ist_Store(ADDR address, DataTy data) {
        CODEBLOCKISWRITECHECK(address);
        PAGE* P = getMemPage(address);
        MEM_ACCESS_ASSERT_W(P, address);
        CheckSelf(P, address);
        vassert(P->get_user() == user);
        P->check_ref_cound();
        UShort offset = address & 0xfff;
        if (fastalignD1[sizeof(data) << 3] > 0xFFF - offset) {
            PAGE* nP = getMemPage(address + 0x1000);
            MEM_ACCESS_ASSERT_W(nP, address + 0x1000);
            CheckSelf(nP, address + 0x1000);
            UInt plength = (0x1000 - offset);
            (*P)->Ist_Put(offset, (void*)&data, plength);
            (*nP)->Ist_Put(0, ((UChar*)((void*)&data)) + plength, (sizeof(data) - plength));
        }
        else {
            (*P)->Ist_Put(offset, data);
        }
    }


private:
    template<typename DataTy>
    void Ist_Store_bpt(ADDR address, DataTy data) {
        CODEBLOCKISWRITECHECK(address);
        PAGE* P = getMemPage(address);
        MEM_ACCESS_ASSERT_W(P, address);
        CheckSelf(P, address);
        vassert(P->get_user() == user);
        UShort offset = address & 0xfff;
        if (fastalignD1[sizeof(data) << 3] > 0xFFF - offset) {
            PAGE* nP = getMemPage(address + 0x1000);
            MEM_ACCESS_ASSERT_W(nP, address + 0x1000);
            CheckSelf(nP, address + 0x1000);
            UInt plength = (0x1000 - offset);
            (*P)->Ist_Put(offset, (void*)&data, plength);
            (*nP)->Ist_Put(0, ((UChar*)((void*)&data)) + plength, (sizeof(data) - plength));
        }
        else {
            (*P)->Ist_Put(offset, data);
        }
    }
    void Ist_Store_bpt(ADDR address, Vns const& data) {
        if (data.real()) {
            switch (data.bitn) {
            case 8:  Ist_Store_bpt(address, (UChar)data); break;
            case 16: Ist_Store_bpt(address, (UShort)data); break;
            case 32: Ist_Store_bpt(address, (UInt)data); break;
            case 64: Ist_Store_bpt(address, (ULong)data); break;
            default:
            }
        }
    }

public:


    template<unsigned int bitn>
    void Ist_Store(ADDR address, Z3_ast data) {
        CODEBLOCKISWRITECHECK(address);
        PAGE* P = getMemPage(address);
        MEM_ACCESS_ASSERT_W(P, address);
        CheckSelf(P, address);
        vassert(P->get_user() == user);
        P->check_ref_cound();
        UShort offset = address & 0xfff;
        if (fastalignD1[bitn] > 0xFFF - offset) {
            PAGE* nP = getMemPage(address + 0x1000);
            MEM_ACCESS_ASSERT_W(nP, address + 0x1000);
            CheckSelf(nP, address + 0x1000);
            UInt plength = (0x1000 - offset);
            Z3_ast Low = Z3_mk_extract(m_ctx, (plength << 3) - 1, 0, data);
            Z3_inc_ref(m_ctx, Low);
            Z3_ast HI = Z3_mk_extract(m_ctx, bitn - 1, plength << 3, data);
            Z3_inc_ref(m_ctx, HI);
            (*nP)->Ist_Put(offset, Low, plength);
            (*nP)->Ist_Put(0, HI, (bitn >> 3) - plength);
            Z3_dec_ref(m_ctx, Low);
            Z3_dec_ref(m_ctx, HI);
        }
        else {
            (*P)->Ist_Put<bitn>(offset, data);
        }
    }

    template<typename DataTy>
    void Ist_Store(Z3_ast address, DataTy data) {
        addressingMode<ADDR> am(z3::expr(m_ctx, address));
        auto kind = am.analysis_kind();
        if (kind == addressingMode<ADDR>::support_bit_blast) {
#ifdef TRACE_AM
            printf("Ist_Store base: %p {\n", am.getBase());
            am.print();
            printf("}\n");
#endif
            for (auto offset : am) {
                ADDR raddr = am.getBase() + offset;
                auto oData = Iex_Load<(IRType)(sizeof(DataTy) << 3)>(raddr);
                auto eq = Z3_mk_eq(m_ctx, am.getoffset(), Vns(m_ctx, offset));
                Z3_inc_ref(m_ctx, eq);
                auto n_Data = Z3_mk_ite(m_ctx, eq, Vns(m_ctx, data), oData);
                Z3_inc_ref(m_ctx, n_Data);
                Ist_Store<(IRType)(sizeof(DataTy) << 3)>(raddr, n_Data);
                Z3_dec_ref(m_ctx, n_Data);
                Z3_dec_ref(m_ctx, eq);
            }
        }
        else {
            Itaddress it = this->addr_begin(m_solver, address);
            while (it.check()) {
                Vns addr = *it;
                ADDR addr_re = addr;
                auto oData = Iex_Load<(IRType)(sizeof(DataTy) << 3)>(addr_re);
                auto eq = Z3_mk_eq(m_ctx, address, addr);
                Z3_inc_ref(m_ctx, eq);
                auto n_Data = Z3_mk_ite(m_ctx, eq, Vns(m_ctx, data), oData);
                Z3_inc_ref(m_ctx, n_Data);
                Ist_Store<(IRType)(sizeof(DataTy) << 3)>(addr_re, n_Data);
                Z3_dec_ref(m_ctx, n_Data);
                Z3_dec_ref(m_ctx, eq);
                it++;
            }
        }
    }

    //n_bit
    template<unsigned int bitn>
    void Ist_Store(Z3_ast address, Z3_ast data) {
        uint64_t Z3_RE;
        bool suspend_solve = true;
        LARGE_INTEGER   freq = { 0 };
        LARGE_INTEGER   beginPerformanceCount = { 0 };
        LARGE_INTEGER   closePerformanceCount = { 0 };
        QueryPerformanceFrequency(&freq);
        QueryPerformanceCounter(&beginPerformanceCount);
    redo:
        {
            Itaddress it = this->addr_begin(m_solver, address);
            while (it.check()) {
                if (suspend_solve) {
                    QueryPerformanceCounter(&closePerformanceCount);
                    double delta_seconds = (double)(closePerformanceCount.QuadPart - beginPerformanceCount.QuadPart) / freq.QuadPart;
                    if (delta_seconds > ANALYZER_TIMEOUT) {
                        break;
                    }
                    else {
                        suspend_solve = false;
                    }
                }
                auto addr = *it;
                if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
                auto oData = Iex_Load<(IRType)bitn>(Z3_RE);
                auto eq = Z3_mk_eq(m_ctx, address, addr);
                Z3_inc_ref(m_ctx, eq);
                auto n_Data = Z3_mk_ite(m_ctx, eq, data, oData);
                Z3_inc_ref(m_ctx, n_Data);
                Ist_Store<(IRType)bitn>(Z3_RE, n_Data);
                Z3_dec_ref(m_ctx, n_Data);
                Z3_dec_ref(m_ctx, eq);
                it++;
            }
        }
        if (suspend_solve) {
            addressingMode<ADDR> am(z3::expr(m_ctx, address));
            auto kind = am.analysis_kind();
            if (kind == addressingMode<ADDR>::support_bit_blast) {
#ifdef TRACE_AM
                printf("Ist_Store base: %p {\n", am.getBase());
                am.print();
                printf("}\n");
#endif
                for (auto offset : am) {
                    ADDR raddr = am.getBase() + offset;
                    auto oData = Iex_Load<(IRType)bitn>(raddr);
                    auto eq = Z3_mk_eq(m_ctx, am.getoffset(), Vns(m_ctx, offset));
                    Z3_inc_ref(m_ctx, eq);
                    auto n_Data = Z3_mk_ite(m_ctx, eq, data, oData);
                    Z3_inc_ref(m_ctx, n_Data);
                    Ist_Store<(IRType)bitn>(raddr, n_Data);
                    Z3_dec_ref(m_ctx, n_Data);
                    Z3_dec_ref(m_ctx, eq);
                }
            }
            else {
                suspend_solve = false;
                goto redo;
            }
        }
    }

    inline void Ist_Store(ADDR address, Vns const &data) {
        if (data.real()) {
            switch (data.bitn) {
            case 8:  Ist_Store(address, (UChar)data); break;
            case 16: Ist_Store(address, (UShort)data); break;
            case 32: Ist_Store(address, (UInt)data); break;
            case 64: Ist_Store(address, (ULong)data); break;
            default:
                if (data.bitn == 128) Ist_Store(address, (__m128i)data);
                else {
                    vassert(data.bitn == 256);
                    Ist_Store(address, (__m256i)data);
                }
            }
        }
        else {
            switch (data.bitn) {
            case 8:  Ist_Store<8>(address, (Z3_ast)data); break;
            case 16: Ist_Store<16>(address, (Z3_ast)data); break;
            case 32: Ist_Store<32>(address, (Z3_ast)data); break;
            case 64: Ist_Store<64>(address, (Z3_ast)data); break;
            default:
                if (data.bitn == 128) 
                    Ist_Store<128>(address, (Z3_ast)data);
                else {
                    vassert(data.bitn == 256);
                    Ist_Store<256>(address, (Z3_ast)data); break;
                }
            }
        }
    }


    template<typename DataTy>
    inline void Ist_Store(Vns const &address, DataTy data) {
        if (address.real()) {
            Ist_Store((ADDR)address, data);
        }
        else {
            Ist_Store((Z3_ast)address, data);
        }
    }

    inline void MEM::Ist_Store(Z3_ast address, Vns const &data) {
        if (data.real()) {
            switch (data.bitn) {
            case 8: return Ist_Store(address, (UChar)data);
            case 16:return Ist_Store(address, (UShort)data);
            case 32:return Ist_Store(address, (UInt)data);
            case 64:return Ist_Store(address, (ULong)data);
            case 128:return Ist_Store(address, (__m128i)data);
            case 256:return Ist_Store(address, (__m256i)data);
            default:vpanic("2333333");
            }
        }
        else {
            switch (data.bitn) {
            case 8: return Ist_Store<8>(address, (Z3_ast)data);
            case 16:return Ist_Store<16>(address, (Z3_ast)data);
            case 32:return Ist_Store<32>(address, (Z3_ast)data);
            case 64:return Ist_Store<64>(address, (Z3_ast)data);
            case 128:return Ist_Store<128>(address, (Z3_ast)data);
            case 256:return Ist_Store<256>(address, (Z3_ast)data);
            default:vpanic("2333333");
            }
        }
    }

    inline void MEM::Ist_Store(Vns const &address, Vns const &data) {
        if (address.real()) {
            Ist_Store((ADDR)address, data);
        }
        else {
            Ist_Store((Z3_ast)address, data);
        }
    }

    inline operator Z3_context() { return m_ctx; };
    ;;
private:

    //template<>
    //void Ist_Store(ADDR address, Vns data) = delete;
    //template<>
    //void Ist_Store(ADDR address, Vns &data) = delete;
    //template<>
    //void Ist_Store(ADDR address, Vns const &data) = delete;
    //template<>
    //void Ist_Store(ADDR address, Z3_ast data) = delete;
    //template<>
    //void Ist_Store(ADDR address, Z3_ast &data) = delete;

    //template<>
    //void Ist_Store(Z3_ast address, Vns data) = delete;
    //template<>
    //void Ist_Store(Z3_ast address, Vns &data) = delete;
    //template<>
    //void Ist_Store(Z3_ast address, Vns const &data) = delete;

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
