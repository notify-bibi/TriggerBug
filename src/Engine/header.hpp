/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    header.hpp:
Abstract:
    API list;
Author:
    WXC 2019-05-31.
Revision History:
--*/

#ifndef HEADER_H
#define HEADER_H

extern "C"
{
#include "libvex.h";
#include "libvex_guest_x86.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_arm.h"
#include "libvex_guest_arm64.h"
#include "libvex_guest_ppc32.h"
#include "libvex_guest_ppc64.h"
#include "libvex_guest_mips32.h"
#include "libvex_guest_mips64.h"
#include "libvex_guest_s390x.h"
};

#undef guest_LR
#undef guest_SP
#undef guest_FP

extern "C" Bool vex_initdone;
extern "C" void vex_assert_fail(const HChar * expr, const HChar * file, Int line, const HChar * fn);
extern "C" unsigned int vex_printf(const HChar * format, ...);
extern "C" void vpanic(const HChar * str);


#define __i386__
#define TESTCODE(code)                                                                                                  \
{                                                                                                                       \
    LARGE_INTEGER   freq = { 0 };                                                                                       \
    LARGE_INTEGER   beginPerformanceCount = { 0 };                                                                      \
    LARGE_INTEGER   closePerformanceCount = { 0 };                                                                      \
    QueryPerformanceFrequency(&freq);                                                                                   \
    QueryPerformanceCounter(&beginPerformanceCount);                                                                    \
    {code    }                                                                                                          \
    QueryPerformanceCounter(&closePerformanceCount);                                                                    \
    double delta_seconds = (double)(closePerformanceCount.QuadPart - beginPerformanceCount.QuadPart) / freq.QuadPart;   \
    printf("%s line:%d spend %lf \n",__FILE__, __LINE__, delta_seconds);                                                \
}


#define ALIGN(Value,size) ((Value) & ~((size) - 1))


#define LZDEF(n) ((unsigned char)(((((((int)(n))-1) & -8) + 8) >> 3) - 1))
const UChar fastalignD1[257] = { LZDEF(0),  LZDEF(1),  LZDEF(2),  LZDEF(3),  LZDEF(4),  LZDEF(5),  LZDEF(6),  LZDEF(7),  LZDEF(8),  LZDEF(9),  LZDEF(10),  LZDEF(11),  LZDEF(12),  LZDEF(13),  LZDEF(14),  LZDEF(15),  LZDEF(16),  LZDEF(17),  LZDEF(18),  LZDEF(19),  LZDEF(20),  LZDEF(21),  LZDEF(22),  LZDEF(23),  LZDEF(24),  LZDEF(25),  LZDEF(26),  LZDEF(27),  LZDEF(28),  LZDEF(29),  LZDEF(30),  LZDEF(31),  LZDEF(32),  LZDEF(33),  LZDEF(34),  LZDEF(35),  LZDEF(36),  LZDEF(37),  LZDEF(38),  LZDEF(39),  LZDEF(40),  LZDEF(41),  LZDEF(42),  LZDEF(43),  LZDEF(44),  LZDEF(45),  LZDEF(46),  LZDEF(47),  LZDEF(48),  LZDEF(49),  LZDEF(50),  LZDEF(51),  LZDEF(52),  LZDEF(53),  LZDEF(54),  LZDEF(55),  LZDEF(56),  LZDEF(57),  LZDEF(58),  LZDEF(59),  LZDEF(60),  LZDEF(61),  LZDEF(62),  LZDEF(63),  LZDEF(64),  LZDEF(65),  LZDEF(66),  LZDEF(67),  LZDEF(68),  LZDEF(69),  LZDEF(70),  LZDEF(71),  LZDEF(72),  LZDEF(73),  LZDEF(74),  LZDEF(75),  LZDEF(76),  LZDEF(77),  LZDEF(78),  LZDEF(79),  LZDEF(80),  LZDEF(81),  LZDEF(82),  LZDEF(83),  LZDEF(84),  LZDEF(85),  LZDEF(86),  LZDEF(87),  LZDEF(88),  LZDEF(89),  LZDEF(90),  LZDEF(91),  LZDEF(92),  LZDEF(93),  LZDEF(94),  LZDEF(95),  LZDEF(96),  LZDEF(97),  LZDEF(98),  LZDEF(99),  LZDEF(100),  LZDEF(101),  LZDEF(102),  LZDEF(103),  LZDEF(104),  LZDEF(105),  LZDEF(106),  LZDEF(107),  LZDEF(108),  LZDEF(109),  LZDEF(110),  LZDEF(111),  LZDEF(112),  LZDEF(113),  LZDEF(114),  LZDEF(115),  LZDEF(116),  LZDEF(117),  LZDEF(118),  LZDEF(119),  LZDEF(120),  LZDEF(121),  LZDEF(122),  LZDEF(123),  LZDEF(124),  LZDEF(125),  LZDEF(126),  LZDEF(127),  LZDEF(128),  LZDEF(129),  LZDEF(130),  LZDEF(131),  LZDEF(132),  LZDEF(133),  LZDEF(134),  LZDEF(135),  LZDEF(136),  LZDEF(137),  LZDEF(138),  LZDEF(139),  LZDEF(140),  LZDEF(141),  LZDEF(142),  LZDEF(143),  LZDEF(144),  LZDEF(145),  LZDEF(146),  LZDEF(147),  LZDEF(148),  LZDEF(149),  LZDEF(150),  LZDEF(151),  LZDEF(152),  LZDEF(153),  LZDEF(154),  LZDEF(155),  LZDEF(156),  LZDEF(157),  LZDEF(158),  LZDEF(159),  LZDEF(160),  LZDEF(161),  LZDEF(162),  LZDEF(163),  LZDEF(164),  LZDEF(165),  LZDEF(166),  LZDEF(167),  LZDEF(168),  LZDEF(169),  LZDEF(170),  LZDEF(171),  LZDEF(172),  LZDEF(173),  LZDEF(174),  LZDEF(175),  LZDEF(176),  LZDEF(177),  LZDEF(178),  LZDEF(179),  LZDEF(180),  LZDEF(181),  LZDEF(182),  LZDEF(183),  LZDEF(184),  LZDEF(185),  LZDEF(186),  LZDEF(187),  LZDEF(188),  LZDEF(189),  LZDEF(190),  LZDEF(191),  LZDEF(192),  LZDEF(193),  LZDEF(194),  LZDEF(195),  LZDEF(196),  LZDEF(197),  LZDEF(198),  LZDEF(199),  LZDEF(200),  LZDEF(201),  LZDEF(202),  LZDEF(203),  LZDEF(204),  LZDEF(205),  LZDEF(206),  LZDEF(207),  LZDEF(208),  LZDEF(209),  LZDEF(210),  LZDEF(211),  LZDEF(212),  LZDEF(213),  LZDEF(214),  LZDEF(215),  LZDEF(216),  LZDEF(217),  LZDEF(218),  LZDEF(219),  LZDEF(220),  LZDEF(221),  LZDEF(222),  LZDEF(223),  LZDEF(224),  LZDEF(225),  LZDEF(226),  LZDEF(227),  LZDEF(228),  LZDEF(229),  LZDEF(230),  LZDEF(231),  LZDEF(232),  LZDEF(233),  LZDEF(234),  LZDEF(235),  LZDEF(236),  LZDEF(237),  LZDEF(238),  LZDEF(239),  LZDEF(240),  LZDEF(241),  LZDEF(242),  LZDEF(243),  LZDEF(244),  LZDEF(245),  LZDEF(246),  LZDEF(247),  LZDEF(248),  LZDEF(249),  LZDEF(250),  LZDEF(251),  LZDEF(252),  LZDEF(253),  LZDEF(254),  LZDEF(255),  LZDEF(256) };
#undef  LZDEF
//
//#define LZDEF(n) ((unsigned char)((((((int)(n))-1) & -8) + 8) >> 3))
//const UChar  fastalign[257] = { LZDEF(0),  LZDEF(1),  LZDEF(2),  LZDEF(3),  LZDEF(4),  LZDEF(5),  LZDEF(6),  LZDEF(7),  LZDEF(8),  LZDEF(9),  LZDEF(10),  LZDEF(11),  LZDEF(12),  LZDEF(13),  LZDEF(14),  LZDEF(15),  LZDEF(16),  LZDEF(17),  LZDEF(18),  LZDEF(19),  LZDEF(20),  LZDEF(21),  LZDEF(22),  LZDEF(23),  LZDEF(24),  LZDEF(25),  LZDEF(26),  LZDEF(27),  LZDEF(28),  LZDEF(29),  LZDEF(30),  LZDEF(31),  LZDEF(32),  LZDEF(33),  LZDEF(34),  LZDEF(35),  LZDEF(36),  LZDEF(37),  LZDEF(38),  LZDEF(39),  LZDEF(40),  LZDEF(41),  LZDEF(42),  LZDEF(43),  LZDEF(44),  LZDEF(45),  LZDEF(46),  LZDEF(47),  LZDEF(48),  LZDEF(49),  LZDEF(50),  LZDEF(51),  LZDEF(52),  LZDEF(53),  LZDEF(54),  LZDEF(55),  LZDEF(56),  LZDEF(57),  LZDEF(58),  LZDEF(59),  LZDEF(60),  LZDEF(61),  LZDEF(62),  LZDEF(63),  LZDEF(64),  LZDEF(65),  LZDEF(66),  LZDEF(67),  LZDEF(68),  LZDEF(69),  LZDEF(70),  LZDEF(71),  LZDEF(72),  LZDEF(73),  LZDEF(74),  LZDEF(75),  LZDEF(76),  LZDEF(77),  LZDEF(78),  LZDEF(79),  LZDEF(80),  LZDEF(81),  LZDEF(82),  LZDEF(83),  LZDEF(84),  LZDEF(85),  LZDEF(86),  LZDEF(87),  LZDEF(88),  LZDEF(89),  LZDEF(90),  LZDEF(91),  LZDEF(92),  LZDEF(93),  LZDEF(94),  LZDEF(95),  LZDEF(96),  LZDEF(97),  LZDEF(98),  LZDEF(99),  LZDEF(100),  LZDEF(101),  LZDEF(102),  LZDEF(103),  LZDEF(104),  LZDEF(105),  LZDEF(106),  LZDEF(107),  LZDEF(108),  LZDEF(109),  LZDEF(110),  LZDEF(111),  LZDEF(112),  LZDEF(113),  LZDEF(114),  LZDEF(115),  LZDEF(116),  LZDEF(117),  LZDEF(118),  LZDEF(119),  LZDEF(120),  LZDEF(121),  LZDEF(122),  LZDEF(123),  LZDEF(124),  LZDEF(125),  LZDEF(126),  LZDEF(127),  LZDEF(128),  LZDEF(129),  LZDEF(130),  LZDEF(131),  LZDEF(132),  LZDEF(133),  LZDEF(134),  LZDEF(135),  LZDEF(136),  LZDEF(137),  LZDEF(138),  LZDEF(139),  LZDEF(140),  LZDEF(141),  LZDEF(142),  LZDEF(143),  LZDEF(144),  LZDEF(145),  LZDEF(146),  LZDEF(147),  LZDEF(148),  LZDEF(149),  LZDEF(150),  LZDEF(151),  LZDEF(152),  LZDEF(153),  LZDEF(154),  LZDEF(155),  LZDEF(156),  LZDEF(157),  LZDEF(158),  LZDEF(159),  LZDEF(160),  LZDEF(161),  LZDEF(162),  LZDEF(163),  LZDEF(164),  LZDEF(165),  LZDEF(166),  LZDEF(167),  LZDEF(168),  LZDEF(169),  LZDEF(170),  LZDEF(171),  LZDEF(172),  LZDEF(173),  LZDEF(174),  LZDEF(175),  LZDEF(176),  LZDEF(177),  LZDEF(178),  LZDEF(179),  LZDEF(180),  LZDEF(181),  LZDEF(182),  LZDEF(183),  LZDEF(184),  LZDEF(185),  LZDEF(186),  LZDEF(187),  LZDEF(188),  LZDEF(189),  LZDEF(190),  LZDEF(191),  LZDEF(192),  LZDEF(193),  LZDEF(194),  LZDEF(195),  LZDEF(196),  LZDEF(197),  LZDEF(198),  LZDEF(199),  LZDEF(200),  LZDEF(201),  LZDEF(202),  LZDEF(203),  LZDEF(204),  LZDEF(205),  LZDEF(206),  LZDEF(207),  LZDEF(208),  LZDEF(209),  LZDEF(210),  LZDEF(211),  LZDEF(212),  LZDEF(213),  LZDEF(214),  LZDEF(215),  LZDEF(216),  LZDEF(217),  LZDEF(218),  LZDEF(219),  LZDEF(220),  LZDEF(221),  LZDEF(222),  LZDEF(223),  LZDEF(224),  LZDEF(225),  LZDEF(226),  LZDEF(227),  LZDEF(228),  LZDEF(229),  LZDEF(230),  LZDEF(231),  LZDEF(232),  LZDEF(233),  LZDEF(234),  LZDEF(235),  LZDEF(236),  LZDEF(237),  LZDEF(238),  LZDEF(239),  LZDEF(240),  LZDEF(241),  LZDEF(242),  LZDEF(243),  LZDEF(244),  LZDEF(245),  LZDEF(246),  LZDEF(247),  LZDEF(248),  LZDEF(249),  LZDEF(250),  LZDEF(251),  LZDEF(252),  LZDEF(253),  LZDEF(254),  LZDEF(255),  LZDEF(256) };
//#undef  LZDEF

#define LZDEF(n) ((ULong)((1ull << ((int)n)) - 1))
const ULong fastMask[65] = { LZDEF(0),  LZDEF(1),  LZDEF(2),  LZDEF(3),  LZDEF(4),  LZDEF(5),  LZDEF(6),  LZDEF(7),  LZDEF(8),  LZDEF(9),  LZDEF(10),  LZDEF(11),  LZDEF(12),  LZDEF(13),  LZDEF(14),  LZDEF(15),  LZDEF(16),  LZDEF(17),  LZDEF(18),  LZDEF(19),  LZDEF(20),  LZDEF(21),  LZDEF(22),  LZDEF(23),  LZDEF(24),  LZDEF(25),  LZDEF(26),  LZDEF(27),  LZDEF(28),  LZDEF(29),  LZDEF(30),  LZDEF(31),  LZDEF(32),  LZDEF(33),  LZDEF(34),  LZDEF(35),  LZDEF(36),  LZDEF(37),  LZDEF(38),  LZDEF(39),  LZDEF(40),  LZDEF(41),  LZDEF(42),  LZDEF(43),  LZDEF(44),  LZDEF(45),  LZDEF(46),  LZDEF(47),  LZDEF(48),  LZDEF(49),  LZDEF(50),  LZDEF(51),  LZDEF(52),  LZDEF(53),  LZDEF(54),  LZDEF(55),  LZDEF(56),  LZDEF(57),  LZDEF(58),  LZDEF(59),  LZDEF(60),  LZDEF(61),  LZDEF(62),  LZDEF(63),  -1ULL };
#undef  LZDEF


#define LZDEF(n) ((ULong)((1ull << ((int)n + 1)) - 1))
const ULong fastMaskI1[65] = { LZDEF(0),  LZDEF(1),  LZDEF(2),  LZDEF(3),  LZDEF(4),  LZDEF(5),  LZDEF(6),  LZDEF(7),  LZDEF(8),  LZDEF(9),  LZDEF(10),  LZDEF(11),  LZDEF(12),  LZDEF(13),  LZDEF(14),  LZDEF(15),  LZDEF(16),  LZDEF(17),  LZDEF(18),  LZDEF(19),  LZDEF(20),  LZDEF(21),  LZDEF(22),  LZDEF(23),  LZDEF(24),  LZDEF(25),  LZDEF(26),  LZDEF(27),  LZDEF(28),  LZDEF(29),  LZDEF(30),  LZDEF(31),  LZDEF(32),  LZDEF(33),  LZDEF(34),  LZDEF(35),  LZDEF(36),  LZDEF(37),  LZDEF(38),  LZDEF(39),  LZDEF(40),  LZDEF(41),  LZDEF(42),  LZDEF(43),  LZDEF(44),  LZDEF(45),  LZDEF(46),  LZDEF(47),  LZDEF(48),  LZDEF(49),  LZDEF(50),  LZDEF(51),  LZDEF(52),  LZDEF(53),  LZDEF(54),  LZDEF(55),  LZDEF(56),  LZDEF(57),  LZDEF(58),  LZDEF(59),  LZDEF(60),  LZDEF(61),  LZDEF(62),  -1ULL,  -1ULL };
#undef  LZDEF

#define LZDEF(n) ((ULong)((1ull << ((int)n << 3)) - 1))
const ULong fastMaskB[9] = { LZDEF(0),  LZDEF(1),  LZDEF(2),  LZDEF(3),  LZDEF(4),  LZDEF(5),  LZDEF(6),  LZDEF(7),  -1ULL };
#undef  LZDEF

#define LZDEF(n) ((ULong)( (1ull << (((int)n + 1) << 3)) - 1))
const ULong fastMaskBI1[9] = { LZDEF(0),  LZDEF(1),  LZDEF(2),  LZDEF(3),  LZDEF(4),  LZDEF(5),  LZDEF(6),  -1ULL,  -1ULL };
#undef  LZDEF

#define fastMaskReverse(N) (~fastMask[N])
#define fastMaskReverseI1(N) (~fastMaskI1[N])
#define Z3_Get_Ref(exp) (((int*)((Z3_ast)((exp))))[2])

extern __m256i  m32_fast[33];
extern __m256i  m32_mask_reverse[33];


template <int maxlength> class Register;
template <typename ADDR> class State;
class Kernel;

#ifdef _MSC_VER
#define NORETURN __declspec(noreturn)
#else
#define NORETURN __attribute__ ((noreturn))
#endif
typedef enum :unsigned int {
    NewState = 0,
    Running,
    Fork,
    Death,
    Exit,
    NoDecode,
    Exception,
    Dirty_ret
}State_Tag;

/* vex_traceflags values */
#define VEX_TRACE_FE     (1 << 7)  /* show conversion into IR */
#define VEX_TRACE_OPT1   (1 << 6)  /* show after initial opt */
#define VEX_TRACE_INST   (1 << 5)  /* show after instrumentation */
#define VEX_TRACE_OPT2   (1 << 4)  /* show after second opt */
#define VEX_TRACE_TREES  (1 << 3)  /* show after tree building */
#define VEX_TRACE_VCODE  (1 << 2)  /* show selected insns */
#define VEX_TRACE_RCODE  (1 << 1)  /* show after reg-alloc */
#define VEX_TRACE_ASM    (1 << 0)  /* show final assembly */


#define SET1(addr, value) *(UChar*)((addr)) = (value)
#define SET2(addr, value) *(UShort*)((addr)) = (value)
#define SET4(addr, value) *(UInt*)((addr)) = (value)
#define SET8(addr, value) *(ULong*)((addr)) = (value)
#define SET16(addr, value) *(__m128i*)((addr)) = (value)
#define SET32(addr, value) *(__m256i*)((addr)) = (value)

#define GET1(addr) (*(UChar*)((addr))) 
#define GET2(addr) (*(UShort*)((addr)))
#define GET4(addr) (*(UInt*)((addr)))
#define GET8(addr) (*(ULong*)((addr)))
#define GET16(addr) (*(__m128i*)((addr)))
#define GET32(addr) (*(__m256i*)((addr)))


#define GETS1(addr) (*(Char*)((addr))) 
#define GETS2(addr) (*(Short*)((addr)))
#define GETS4(addr) (*(Int*)((addr)))
#define GETS8(addr) (*(Long*)((addr)))
#define GETS16(addr) (*(__m128i*)((addr)))
#define GETS32(addr) (*(__m256i*)((addr)))

#define MV1(addr,fromaddr) *(UChar*)((addr))=(*(UChar*)((fromaddr))) 
#define MV2(addr,fromaddr) *(UShort*)((addr))=(*(UShort*)((fromaddr)))
#define MV4(addr,fromaddr) *(UInt*)((addr))=(*(UInt*)((fromaddr)))
#define MV8(addr,fromaddr) *(ULong*)((addr))=(*(ULong*)((fromaddr)))
#define MV16(addr,fromaddr) *(__m128i*)((addr))=(*(__m128i*)((fromaddr)))
#define MV32(addr,fromaddr) *(__m256i*)((addr))=(*(__m256i*)((fromaddr)))

typedef enum:unsigned char {
    nothing,
    symbolic,
    numreal
}memTAG;


typedef enum :UChar {
    unknowSystem = 0b00,
    linux,
    windows
}GuestSystem;


typedef enum :ULong {
    CF_None = 0,
    CF_ppStmts = 1ull,
    CF_traceJmp = 1ull << 1,
    CF_traceState = 1ull << 2,
    CF_TraceSymbolic = 1ull << 3,
    CF_PassSigSEGV = 1ull << 4,
}TRControlFlags;


namespace TRtype {
    typedef State_Tag(*Hook_CB)         (Kernel*);
    //得到的ast无需Z3_inc_ref
    typedef Z3_ast(*TableIdx_CB) (Kernel*, Addr64 /*base*/, Z3_ast /*idx*/);
};

typedef struct _Hook_ {
    TRtype::Hook_CB cb;
    UChar original;
    TRControlFlags cflag;
}Hook_struct;


inline __m128i _mm_not_si128(__m128i a) {
    __m128i r;
    r.m128i_u64[0] = ~a.m128i_u64[0];
    r.m128i_u64[1] = ~a.m128i_u64[1];
    return  r;
}

inline __m256i _mm256_not_si256(__m256i a) {
    __m256i r;
    r.m256i_u64[0] = ~a.m256i_u64[0];
    r.m256i_u64[1] = ~a.m256i_u64[1];
    r.m256i_u64[2] = ~a.m256i_u64[2];
    r.m256i_u64[3] = ~a.m256i_u64[3];
    return r;
}

inline Z3_ast Z3_mk_neq(Z3_context ctx, Z3_ast a, Z3_ast b) {
    Z3_ast args[2] = { a, b };
    return Z3_mk_distinct(ctx, 2, args);;
}


//C:\Python37\python.exe C : / Users / bibi / Desktop / TriggerBug / src / Engine / guest_arch_state_regs_layout_template_print.py
#define X86_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestX86State, guest_##REGNAME)
#define X86_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestX86State::guest_##REGNAME)
#define X86_ALL_REGS_DEF(_macro) \
_macro(EAX),\
_macro(ECX),\
_macro(EDX),\
_macro(EBX),\
_macro(ESP),\
_macro(EBP),\
_macro(ESI),\
_macro(EDI),\
_macro(CC_OP),\
_macro(CC_DEP1),\
_macro(CC_DEP2),\
_macro(CC_NDEP),\
_macro(DFLAG),\
_macro(IDFLAG),\
_macro(ACFLAG),\
_macro(EIP),\
_macro(FPREG),\
_macro(FPTAG),\
_macro(FPROUND),\
_macro(FC3210),\
_macro(FTOP),\
_macro(SSEROUND),\
_macro(XMM0),\
_macro(XMM1),\
_macro(XMM2),\
_macro(XMM3),\
_macro(XMM4),\
_macro(XMM5),\
_macro(XMM6),\
_macro(XMM7),\
_macro(CS),\
_macro(DS),\
_macro(ES),\
_macro(FS),\
_macro(GS),\
_macro(SS),\
_macro(LDT),\
_macro(GDT),\
_macro(EMNOTE),\
_macro(CMSTART),\
_macro(CMLEN),\
_macro(NRADDR),\
_macro(SC_CLASS),\
_macro(IP_AT_SYSCALL)


#define AMD64_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestAMD64State, guest_##REGNAME)
#define AMD64_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestAMD64State::guest_##REGNAME)
#define AMD64_ALL_REGS_DEF(_macro) \
_macro(RAX),\
_macro(RCX),\
_macro(RDX),\
_macro(RBX),\
_macro(RSP),\
_macro(RBP),\
_macro(RSI),\
_macro(RDI),\
_macro(R8),\
_macro(R9),\
_macro(R10),\
_macro(R11),\
_macro(R12),\
_macro(R13),\
_macro(R14),\
_macro(R15),\
_macro(CC_OP),\
_macro(CC_DEP1),\
_macro(CC_DEP2),\
_macro(CC_NDEP),\
_macro(DFLAG),\
_macro(RIP),\
_macro(ACFLAG),\
_macro(IDFLAG),\
_macro(FS_CONST),\
_macro(SSEROUND),\
_macro(YMM0),\
_macro(YMM1),\
_macro(YMM2),\
_macro(YMM3),\
_macro(YMM4),\
_macro(YMM5),\
_macro(YMM6),\
_macro(YMM7),\
_macro(YMM8),\
_macro(YMM9),\
_macro(YMM10),\
_macro(YMM11),\
_macro(YMM12),\
_macro(YMM13),\
_macro(YMM14),\
_macro(YMM15),\
_macro(YMM16),\
_macro(FTOP),\
_macro(FPREG),\
_macro(FPTAG),\
_macro(FPROUND),\
_macro(FC3210),\
_macro(EMNOTE),\
_macro(CMSTART),\
_macro(CMLEN),\
_macro(NRADDR),\
_macro(SC_CLASS),\
_macro(GS_CONST),\
_macro(IP_AT_SYSCALL)


#define ARM_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestARMState, guest_##REGNAME)
#define ARM_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestARMState::guest_##REGNAME)
#define ARM_ALL_REGS_DEF(_macro) \
_macro(R0),\
_macro(R1),\
_macro(R2),\
_macro(R3),\
_macro(R4),\
_macro(R5),\
_macro(R6),\
_macro(R7),\
_macro(R8),\
_macro(R9),\
_macro(R10),\
_macro(R11),\
_macro(R12),\
_macro(R13),\
_macro(R14),\
_macro(R15T),\
_macro(CC_OP),\
_macro(CC_DEP1),\
_macro(CC_DEP2),\
_macro(CC_NDEP),\
_macro(QFLAG32),\
_macro(GEFLAG0),\
_macro(GEFLAG1),\
_macro(GEFLAG2),\
_macro(GEFLAG3),\
_macro(EMNOTE),\
_macro(CMSTART),\
_macro(CMLEN),\
_macro(NRADDR),\
_macro(IP_AT_SYSCALL),\
_macro(D0),\
_macro(D1),\
_macro(D2),\
_macro(D3),\
_macro(D4),\
_macro(D5),\
_macro(D6),\
_macro(D7),\
_macro(D8),\
_macro(D9),\
_macro(D10),\
_macro(D11),\
_macro(D12),\
_macro(D13),\
_macro(D14),\
_macro(D15),\
_macro(D16),\
_macro(D17),\
_macro(D18),\
_macro(D19),\
_macro(D20),\
_macro(D21),\
_macro(D22),\
_macro(D23),\
_macro(D24),\
_macro(D25),\
_macro(D26),\
_macro(D27),\
_macro(D28),\
_macro(D29),\
_macro(D30),\
_macro(D31),\
_macro(FPSCR),\
_macro(TPIDRURO),\
_macro(TPIDRURW),\
_macro(ITSTATE)


#define ARM64_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestARM64State, guest_##REGNAME)
#define ARM64_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestARM64State::guest_##REGNAME)
#define ARM64_ALL_REGS_DEF(_macro) \
_macro(X0),\
_macro(X1),\
_macro(X2),\
_macro(X3),\
_macro(X4),\
_macro(X5),\
_macro(X6),\
_macro(X7),\
_macro(X8),\
_macro(X9),\
_macro(X10),\
_macro(X11),\
_macro(X12),\
_macro(X13),\
_macro(X14),\
_macro(X15),\
_macro(X16),\
_macro(X17),\
_macro(X18),\
_macro(X19),\
_macro(X20),\
_macro(X21),\
_macro(X22),\
_macro(X23),\
_macro(X24),\
_macro(X25),\
_macro(X26),\
_macro(X27),\
_macro(X28),\
_macro(X29),\
_macro(X30),\
_macro(XSP),\
_macro(PC),\
_macro(CC_OP),\
_macro(CC_DEP1),\
_macro(CC_DEP2),\
_macro(CC_NDEP),\
_macro(TPIDR_EL0),\
_macro(Q0),\
_macro(Q1),\
_macro(Q2),\
_macro(Q3),\
_macro(Q4),\
_macro(Q5),\
_macro(Q6),\
_macro(Q7),\
_macro(Q8),\
_macro(Q9),\
_macro(Q10),\
_macro(Q11),\
_macro(Q12),\
_macro(Q13),\
_macro(Q14),\
_macro(Q15),\
_macro(Q16),\
_macro(Q17),\
_macro(Q18),\
_macro(Q19),\
_macro(Q20),\
_macro(Q21),\
_macro(Q22),\
_macro(Q23),\
_macro(Q24),\
_macro(Q25),\
_macro(Q26),\
_macro(Q27),\
_macro(Q28),\
_macro(Q29),\
_macro(Q30),\
_macro(Q31),\
_macro(QCFLAG),\
_macro(EMNOTE),\
_macro(CMSTART),\
_macro(CMLEN),\
_macro(NRADDR),\
_macro(IP_AT_SYSCALL),\
_macro(FPCR),\
_macro(LLSC_SIZE),\
_macro(LLSC_ADDR),\
_macro(LLSC_DATA)


#define PPC32_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestPPC32State, guest_##REGNAME)
#define PPC32_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestPPC32State::guest_##REGNAME)
#define PPC32_ALL_REGS_DEF(_macro) \
_macro(GPR0),\
_macro(GPR1),\
_macro(GPR2),\
_macro(GPR3),\
_macro(GPR4),\
_macro(GPR5),\
_macro(GPR6),\
_macro(GPR7),\
_macro(GPR8),\
_macro(GPR9),\
_macro(GPR10),\
_macro(GPR11),\
_macro(GPR12),\
_macro(GPR13),\
_macro(GPR14),\
_macro(GPR15),\
_macro(GPR16),\
_macro(GPR17),\
_macro(GPR18),\
_macro(GPR19),\
_macro(GPR20),\
_macro(GPR21),\
_macro(GPR22),\
_macro(GPR23),\
_macro(GPR24),\
_macro(GPR25),\
_macro(GPR26),\
_macro(GPR27),\
_macro(GPR28),\
_macro(GPR29),\
_macro(GPR30),\
_macro(GPR31),\
_macro(VSR0),\
_macro(VSR1),\
_macro(VSR2),\
_macro(VSR3),\
_macro(VSR4),\
_macro(VSR5),\
_macro(VSR6),\
_macro(VSR7),\
_macro(VSR8),\
_macro(VSR9),\
_macro(VSR10),\
_macro(VSR11),\
_macro(VSR12),\
_macro(VSR13),\
_macro(VSR14),\
_macro(VSR15),\
_macro(VSR16),\
_macro(VSR17),\
_macro(VSR18),\
_macro(VSR19),\
_macro(VSR20),\
_macro(VSR21),\
_macro(VSR22),\
_macro(VSR23),\
_macro(VSR24),\
_macro(VSR25),\
_macro(VSR26),\
_macro(VSR27),\
_macro(VSR28),\
_macro(VSR29),\
_macro(VSR30),\
_macro(VSR31),\
_macro(VSR32),\
_macro(VSR33),\
_macro(VSR34),\
_macro(VSR35),\
_macro(VSR36),\
_macro(VSR37),\
_macro(VSR38),\
_macro(VSR39),\
_macro(VSR40),\
_macro(VSR41),\
_macro(VSR42),\
_macro(VSR43),\
_macro(VSR44),\
_macro(VSR45),\
_macro(VSR46),\
_macro(VSR47),\
_macro(VSR48),\
_macro(VSR49),\
_macro(VSR50),\
_macro(VSR51),\
_macro(VSR52),\
_macro(VSR53),\
_macro(VSR54),\
_macro(VSR55),\
_macro(VSR56),\
_macro(VSR57),\
_macro(VSR58),\
_macro(VSR59),\
_macro(VSR60),\
_macro(VSR61),\
_macro(VSR62),\
_macro(VSR63),\
_macro(CIA),\
_macro(LR),\
_macro(CTR),\
_macro(XER_SO),\
_macro(XER_OV),\
_macro(XER_OV32),\
_macro(XER_CA),\
_macro(XER_CA32),\
_macro(XER_BC),\
_macro(CR0_321),\
_macro(CR0_0),\
_macro(CR1_321),\
_macro(CR1_0),\
_macro(CR2_321),\
_macro(CR2_0),\
_macro(CR3_321),\
_macro(CR3_0),\
_macro(CR4_321),\
_macro(CR4_0),\
_macro(CR5_321),\
_macro(CR5_0),\
_macro(CR6_321),\
_macro(CR6_0),\
_macro(CR7_321),\
_macro(CR7_0),\
_macro(FPROUND),\
_macro(DFPROUND),\
_macro(C_FPCC),\
_macro(VRSAVE),\
_macro(VSCR),\
_macro(EMNOTE),\
_macro(CMSTART),\
_macro(CMLEN),\
_macro(NRADDR),\
_macro(NRADDR_GPR2),\
_macro(REDIR_SP),\
_macro(REDIR_STACK),\
_macro(IP_AT_SYSCALL),\
_macro(SPRG3_RO),\
_macro(TFHAR),\
_macro(TEXASR),\
_macro(TFIAR),\
_macro(PPR),\
_macro(TEXASRU),\
_macro(PSPB),\
_macro(DSCR)


#define PPC64_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestPPC64State, guest_##REGNAME)
#define PPC64_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestPPC64State::guest_##REGNAME)
#define PPC64_ALL_REGS_DEF(_macro) \
_macro(GPR0),\
_macro(GPR1),\
_macro(GPR2),\
_macro(GPR3),\
_macro(GPR4),\
_macro(GPR5),\
_macro(GPR6),\
_macro(GPR7),\
_macro(GPR8),\
_macro(GPR9),\
_macro(GPR10),\
_macro(GPR11),\
_macro(GPR12),\
_macro(GPR13),\
_macro(GPR14),\
_macro(GPR15),\
_macro(GPR16),\
_macro(GPR17),\
_macro(GPR18),\
_macro(GPR19),\
_macro(GPR20),\
_macro(GPR21),\
_macro(GPR22),\
_macro(GPR23),\
_macro(GPR24),\
_macro(GPR25),\
_macro(GPR26),\
_macro(GPR27),\
_macro(GPR28),\
_macro(GPR29),\
_macro(GPR30),\
_macro(GPR31),\
_macro(VSR0),\
_macro(VSR1),\
_macro(VSR2),\
_macro(VSR3),\
_macro(VSR4),\
_macro(VSR5),\
_macro(VSR6),\
_macro(VSR7),\
_macro(VSR8),\
_macro(VSR9),\
_macro(VSR10),\
_macro(VSR11),\
_macro(VSR12),\
_macro(VSR13),\
_macro(VSR14),\
_macro(VSR15),\
_macro(VSR16),\
_macro(VSR17),\
_macro(VSR18),\
_macro(VSR19),\
_macro(VSR20),\
_macro(VSR21),\
_macro(VSR22),\
_macro(VSR23),\
_macro(VSR24),\
_macro(VSR25),\
_macro(VSR26),\
_macro(VSR27),\
_macro(VSR28),\
_macro(VSR29),\
_macro(VSR30),\
_macro(VSR31),\
_macro(VSR32),\
_macro(VSR33),\
_macro(VSR34),\
_macro(VSR35),\
_macro(VSR36),\
_macro(VSR37),\
_macro(VSR38),\
_macro(VSR39),\
_macro(VSR40),\
_macro(VSR41),\
_macro(VSR42),\
_macro(VSR43),\
_macro(VSR44),\
_macro(VSR45),\
_macro(VSR46),\
_macro(VSR47),\
_macro(VSR48),\
_macro(VSR49),\
_macro(VSR50),\
_macro(VSR51),\
_macro(VSR52),\
_macro(VSR53),\
_macro(VSR54),\
_macro(VSR55),\
_macro(VSR56),\
_macro(VSR57),\
_macro(VSR58),\
_macro(VSR59),\
_macro(VSR60),\
_macro(VSR61),\
_macro(VSR62),\
_macro(VSR63),\
_macro(CIA),\
_macro(LR),\
_macro(CTR),\
_macro(XER_SO),\
_macro(XER_OV),\
_macro(XER_OV32),\
_macro(XER_CA),\
_macro(XER_CA32),\
_macro(XER_BC),\
_macro(CR0_321),\
_macro(CR0_0),\
_macro(CR1_321),\
_macro(CR1_0),\
_macro(CR2_321),\
_macro(CR2_0),\
_macro(CR3_321),\
_macro(CR3_0),\
_macro(CR4_321),\
_macro(CR4_0),\
_macro(CR5_321),\
_macro(CR5_0),\
_macro(CR6_321),\
_macro(CR6_0),\
_macro(CR7_321),\
_macro(CR7_0),\
_macro(FPROUND),\
_macro(DFPROUND),\
_macro(C_FPCC),\
_macro(VRSAVE),\
_macro(VSCR),\
_macro(EMNOTE),\
_macro(CMSTART),\
_macro(CMLEN),\
_macro(NRADDR),\
_macro(NRADDR_GPR2),\
_macro(REDIR_SP),\
_macro(REDIR_STACK),\
_macro(IP_AT_SYSCALL),\
_macro(SPRG3_RO),\
_macro(TFHAR),\
_macro(TEXASR),\
_macro(TFIAR),\
_macro(PPR),\
_macro(TEXASRU),\
_macro(PSPB),\
_macro(DSCR)


#define S390X_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestS390XState, guest_##REGNAME)
#define S390X_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestS390XState::guest_##REGNAME)
#define S390X_ALL_REGS_DEF(_macro) \
_macro(a0),\
_macro(a1),\
_macro(a2),\
_macro(a3),\
_macro(a4),\
_macro(a5),\
_macro(a6),\
_macro(a7),\
_macro(a8),\
_macro(a9),\
_macro(a10),\
_macro(a11),\
_macro(a12),\
_macro(a13),\
_macro(a14),\
_macro(a15),\
_macro(v0),\
_macro(v1),\
_macro(v2),\
_macro(v3),\
_macro(v4),\
_macro(v5),\
_macro(v6),\
_macro(v7),\
_macro(v8),\
_macro(v9),\
_macro(v10),\
_macro(v11),\
_macro(v12),\
_macro(v13),\
_macro(v14),\
_macro(v15),\
_macro(v16),\
_macro(v17),\
_macro(v18),\
_macro(v19),\
_macro(v20),\
_macro(v21),\
_macro(v22),\
_macro(v23),\
_macro(v24),\
_macro(v25),\
_macro(v26),\
_macro(v27),\
_macro(v28),\
_macro(v29),\
_macro(v30),\
_macro(v31),\
_macro(r0),\
_macro(r1),\
_macro(r2),\
_macro(r3),\
_macro(r4),\
_macro(r5),\
_macro(r6),\
_macro(r7),\
_macro(r8),\
_macro(r9),\
_macro(r10),\
_macro(r11),\
_macro(r12),\
_macro(r13),\
_macro(r14),\
_macro(r15),\
_macro(counter),\
_macro(fpc),\
_macro(IA),\
_macro(SYSNO),\
_macro(CC_OP),\
_macro(CC_DEP1),\
_macro(CC_DEP2),\
_macro(CC_NDEP),\
_macro(NRADDR),\
_macro(CMSTART),\
_macro(CMLEN),\
_macro(IP_AT_SYSCALL),\
_macro(EMNOTE)


#define MIPS32_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestMIPS32State, guest_##REGNAME)
#define MIPS32_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestMIPS32State::guest_##REGNAME)
#define MIPS32_ALL_REGS_DEF(_macro) \
_macro(r0),\
_macro(r1),\
_macro(r2),\
_macro(r3),\
_macro(r4),\
_macro(r5),\
_macro(r6),\
_macro(r7),\
_macro(r8),\
_macro(r9),\
_macro(r10),\
_macro(r11),\
_macro(r12),\
_macro(r13),\
_macro(r14),\
_macro(r15),\
_macro(r16),\
_macro(r17),\
_macro(r18),\
_macro(r19),\
_macro(r20),\
_macro(r21),\
_macro(r22),\
_macro(r23),\
_macro(r24),\
_macro(r25),\
_macro(r26),\
_macro(r27),\
_macro(r28),\
_macro(r29),\
_macro(r30),\
_macro(r31),\
_macro(PC),\
_macro(HI),\
_macro(LO),\
_macro(f0),\
_macro(f1),\
_macro(f2),\
_macro(f3),\
_macro(f4),\
_macro(f5),\
_macro(f6),\
_macro(f7),\
_macro(f8),\
_macro(f9),\
_macro(f10),\
_macro(f11),\
_macro(f12),\
_macro(f13),\
_macro(f14),\
_macro(f15),\
_macro(f16),\
_macro(f17),\
_macro(f18),\
_macro(f19),\
_macro(f20),\
_macro(f21),\
_macro(f22),\
_macro(f23),\
_macro(f24),\
_macro(f25),\
_macro(f26),\
_macro(f27),\
_macro(f28),\
_macro(f29),\
_macro(f30),\
_macro(f31),\
_macro(FIR),\
_macro(FCCR),\
_macro(FEXR),\
_macro(FENR),\
_macro(FCSR),\
_macro(ULR),\
_macro(EMNOTE),\
_macro(CMSTART),\
_macro(CMLEN),\
_macro(NRADDR),\
_macro(COND),\
_macro(DSPControl),\
_macro(ac0),\
_macro(ac1),\
_macro(ac2),\
_macro(ac3),\
_macro(CP0_status),\
_macro(CP0_Config5),\
_macro(LLaddr),\
_macro(LLdata),\
_macro(w0),\
_macro(w1),\
_macro(w2),\
_macro(w3),\
_macro(w4),\
_macro(w5),\
_macro(w6),\
_macro(w7),\
_macro(w8),\
_macro(w9),\
_macro(w10),\
_macro(w11),\
_macro(w12),\
_macro(w13),\
_macro(w14),\
_macro(w15),\
_macro(w16),\
_macro(w17),\
_macro(w18),\
_macro(w19),\
_macro(w20),\
_macro(w21),\
_macro(w22),\
_macro(w23),\
_macro(w24),\
_macro(w25),\
_macro(w26),\
_macro(w27),\
_macro(w28),\
_macro(w29),\
_macro(w30),\
_macro(w31),\
_macro(MSACSR)


#define MIPS64_REGS_offset_DEF(REGNAME) REGNAME = offsetof(VexGuestMIPS64State, guest_##REGNAME)
#define MIPS64_REGS_size_DEF(REGNAME) REGNAME = sizeof(VexGuestMIPS64State::guest_##REGNAME)
#define MIPS64_ALL_REGS_DEF(_macro) \
_macro(r0),\
_macro(r1),\
_macro(r2),\
_macro(r3),\
_macro(r4),\
_macro(r5),\
_macro(r6),\
_macro(r7),\
_macro(r8),\
_macro(r9),\
_macro(r10),\
_macro(r11),\
_macro(r12),\
_macro(r13),\
_macro(r14),\
_macro(r15),\
_macro(r16),\
_macro(r17),\
_macro(r18),\
_macro(r19),\
_macro(r20),\
_macro(r21),\
_macro(r22),\
_macro(r23),\
_macro(r24),\
_macro(r25),\
_macro(r26),\
_macro(r27),\
_macro(r28),\
_macro(r29),\
_macro(r30),\
_macro(r31),\
_macro(PC),\
_macro(HI),\
_macro(LO),\
_macro(f0),\
_macro(f1),\
_macro(f2),\
_macro(f3),\
_macro(f4),\
_macro(f5),\
_macro(f6),\
_macro(f7),\
_macro(f8),\
_macro(f9),\
_macro(f10),\
_macro(f11),\
_macro(f12),\
_macro(f13),\
_macro(f14),\
_macro(f15),\
_macro(f16),\
_macro(f17),\
_macro(f18),\
_macro(f19),\
_macro(f20),\
_macro(f21),\
_macro(f22),\
_macro(f23),\
_macro(f24),\
_macro(f25),\
_macro(f26),\
_macro(f27),\
_macro(f28),\
_macro(f29),\
_macro(f30),\
_macro(f31),\
_macro(FIR),\
_macro(FCCR),\
_macro(FEXR),\
_macro(FENR),\
_macro(FCSR),\
_macro(CP0_status),\
_macro(ULR),\
_macro(EMNOTE),\
_macro(COND),\
_macro(CMSTART),\
_macro(CMLEN),\
_macro(NRADDR),\
_macro(LLaddr),\
_macro(LLdata),\
_macro(w0),\
_macro(w1),\
_macro(w2),\
_macro(w3),\
_macro(w4),\
_macro(w5),\
_macro(w6),\
_macro(w7),\
_macro(w8),\
_macro(w9),\
_macro(w10),\
_macro(w11),\
_macro(w12),\
_macro(w13),\
_macro(w14),\
_macro(w15),\
_macro(w16),\
_macro(w17),\
_macro(w18),\
_macro(w19),\
_macro(w20),\
_macro(w21),\
_macro(w22),\
_macro(w23),\
_macro(w24),\
_macro(w25),\
_macro(w26),\
_macro(w27),\
_macro(w28),\
_macro(w29),\
_macro(w30),\
_macro(w31),\
_macro(MSACSR)



//Process finished with exit code 0



#define GUEST_RGS_DEF(GUEST_ARCH)\
namespace GUEST_ARCH##_IR_OFFSET { typedef enum :unsigned int { GUEST_ARCH##_ALL_REGS_DEF(GUEST_ARCH##_REGS_offset_DEF) } GUEST_ARCH##_IR_OFFSET; };\
namespace GUEST_ARCH##_IR_SIZE   { typedef enum :unsigned int { GUEST_ARCH##_ALL_REGS_DEF(GUEST_ARCH##_REGS_size_DEF  ) } GUEST_ARCH##_IR_SIZE  ; };



GUEST_RGS_DEF(X86)
GUEST_RGS_DEF(AMD64)
GUEST_RGS_DEF(ARM)
GUEST_RGS_DEF(ARM64)
GUEST_RGS_DEF(S390X)
GUEST_RGS_DEF(MIPS32)
GUEST_RGS_DEF(MIPS64)
GUEST_RGS_DEF(PPC32)
GUEST_RGS_DEF(PPC64)



#endif // HEADER_H

