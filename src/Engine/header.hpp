#ifndef HEADER_H
#define HEADER_H

#define HOSTARCH VexArchAMD64
#define GUEST_IS_64 
#define __i386__

#define Z3_Get_Ref(exp) (((int*)((Z3_ast)((exp))))[2])

#if defined(GUEST_IS_64)
#define ADDR unsigned long long
#else
#define ADDR unsigned int
#endif

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

#define mem_w(addr_in, value) state->mem.Ist_Store_R((Addr64)(&(addr_in)), value);
#define reg_r(offset, Ity) state->regs.Iex_Get(offset, Ity)


#define ALIGN(Value,size) ((Value) & ~((size) - 1))

extern "C" 
{
#include "../Valgrind/pub/libvex.h";
}
extern "C" Bool vex_initdone;
//extern "C" unsigned char tid2temp[0x10000];
extern "C" tid_type register_tid(unsigned int);
extern "C" tid_type unregister_tid(unsigned int);
extern "C" void tempmeminit();
extern "C" void init_threads_id();
extern "C" void vex_assert_fail(const HChar* expr,const HChar* file, Int line, const HChar* fn);
extern "C" unsigned int vex_printf(const HChar* format, ...);
extern "C" void vpanic(const HChar* str);


extern unsigned char fastalignD1[257 ];
extern unsigned char fastalign[257];
extern ULong fastMask[65];
extern ULong fastMaskI1[65];
extern ULong fastMaskB[9];
extern ULong fastMaskBI1[9];
extern ULong fastMaskReverse[65];
extern ULong fastMaskReverseI1[65];
extern __m256i  m32_fast[33];
extern __m256i  m32_mask_reverse[33];


template <int maxlength> class Register;
class State;

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
    NoDecode,
    Exception
}State_Tag;


typedef enum :unsigned int {
    TRMemory,TRRegister
}Storage;

namespace TRtype {
typedef State_Tag   (*Hook_CB)         (State *);
//得到的ast无需添加Z3_inc_ref
typedef Z3_ast      (*TableIdx_CB) (State*, ADDR /*base*/, Z3_ast /*idx*/);
}

typedef struct _Hook {
    TRtype::Hook_CB cb;
    UChar original;
}Hook_struct;

typedef struct {
    Storage kind;
    ADDR address;
    ADDR r_offset;
    IRType ty;
}Hook_Replace;

#if defined(_DEBUG)
#undef dassert
#define dassert(xexpr)                                           \
  ((void) ((xexpr) ? 0 :                                        \
           (vex_assert_fail (#xexpr,                            \
                             __FILE__, __LINE__,                \
                             __FUNCSIG__), 0)))
#else
#define dassert(...) 
#endif // _DEBUG

#define vassert(xexpr)                                           \
  ((void) ((xexpr) ? 0 :                                         \
           (vex_assert_fail (#xexpr,                             \
                             __FILE__, __LINE__,                 \
                             __FUNCSIG__), 0)))

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
    auto eq = Z3_mk_eq(ctx, a, b);
    Z3_inc_ref(ctx, eq);
    auto re = Z3_mk_not(ctx, eq);
    Z3_dec_ref(ctx, eq);
    return re;
}

extern std::string replace(const char *pszSrc, const char *pszOld, const char *pszNew);
extern unsigned char * _n_page_mem(void *);
extern LARGE_INTEGER   freq_global;
extern LARGE_INTEGER   beginPerformanceCount_global;
extern LARGE_INTEGER   closePerformanceCount_global;
extern State * _states[MAX_THREADS];
#define current_state() _states[temp_index()]


namespace X86_IR_OFFSET {

    typedef enum :unsigned int {
        eax = 8,
        ax = 8,
        al = 8,
        ah = 9,
        ecx = 12,
        cx = 12,
        cl = 12,
        ch = 13,
        edx = 16,
        dx = 16,
        dl = 16,
        dh = 17,
        ebx = 20,
        bx = 20,
        bl = 20,
        bh = 21,
        esp = 24,
        sp = 24,
        ebp = 28,
        bp = 28,
        esi = 32,
        si = 32,
        sil = 32,
        sih = 33,
        edi = 36,
        di = 36,
        dil = 36,
        dih = 37,
        cc_op = 40,
        cc_dep1 = 44,
        cc_dep2 = 48,
        cc_ndep = 52,
        d = 56,
        dflag = 56,
        id = 60,
        idflag = 60,
        ac = 64,
        acflag = 64,
        eip = 68,
        ip = 68,
        pc = 68,
        fpreg = 72,
        fpu_regs = 72,
        mm0 = 72,
        mm1 = 80,
        mm2 = 88,
        mm3 = 96,
        mm4 = 104,
        mm5 = 112,
        mm6 = 120,
        mm7 = 128,
        fptag = 136,
        fpu_tags = 136,
        fpround = 144,
        fc3210 = 148,
        ftop = 152,
        sseround = 156,
        xmm0 = 160,
        xmm1 = 176,
        xmm2 = 192,
        xmm3 = 208,
        xmm4 = 224,
        xmm5 = 240,
        xmm6 = 256,
        xmm7 = 272,
        cs = 288,
        ds = 290,
        es = 292,
        fs = 294,
        gs = 296,
        ss = 298,
        ldt = 304,
        gdt = 312,
        emnote = 320,
        cmstart = 324,
        cmlen = 328,
        nraddr = 332,
        sc_class = 336,
        ip_at_syscall = 340
    }X86_IR_OFFSET;

}



namespace X86_IR_SIZE {
    typedef enum :unsigned int {
        eax = 4,
        ax = 2,
        al = 1,
        ah = 1,
        ecx = 4,
        cx = 2,
        cl = 1,
        ch = 1,
        edx = 4,
        dx = 2,
        dl = 1,
        dh = 1,
        ebx = 4,
        bx = 2,
        bl = 1,
        bh = 1,
        esp = 4,
        sp = 4,
        ebp = 4,
        bp = 4,
        esi = 4,
        si = 2,
        sil = 1,
        sih = 1,
        edi = 4,
        di = 2,
        dil = 1,
        dih = 1,
        cc_op = 4,
        cc_dep1 = 4,
        cc_dep2 = 4,
        cc_ndep = 4,
        d = 4,
        dflag = 4,
        id = 4,
        idflag = 4,
        ac = 4,
        acflag = 4,
        eip = 4,
        ip = 4,
        pc = 4,
        fpreg = 64,
        fpu_regs = 64,
        mm0 = 8,
        mm1 = 8,
        mm2 = 8,
        mm3 = 8,
        mm4 = 8,
        mm5 = 8,
        mm6 = 8,
        mm7 = 8,
        fptag = 8,
        fpu_tags = 8,
        fpround = 4,
        fc3210 = 4,
        ftop = 4,
        sseround = 4,
        xmm0 = 16,
        xmm1 = 16,
        xmm2 = 16,
        xmm3 = 16,
        xmm4 = 16,
        xmm5 = 16,
        xmm6 = 16,
        xmm7 = 16,
        cs = 2,
        ds = 2,
        es = 2,
        fs = 2,
        gs = 2,
        ss = 2,
        ldt = 8,
        gdt = 8,
        emnote = 4,
        cmstart = 4,
        cmlen = 4,
        nraddr = 4,
        sc_class = 4,
        ip_at_syscall = 4
    }X86_IR_SIZE;

}

namespace AMD64_IR_OFFSET {
    typedef enum :unsigned int {
        rax = 16,
        eax = 16,
        ax = 16,
        al = 16,
        ah = 17,
        rcx = 24,
        ecx = 24,
        cx = 24,
        cl = 24,
        ch = 25,
        rdx = 32,
        edx = 32,
        dx = 32,
        dl = 32,
        dh = 33,
        rbx = 40,
        ebx = 40,
        bx = 40,
        bl = 40,
        bh = 41,
        rsp = 48,
        sp = 48,
        esp = 48,
        rbp = 56,
        bp = 56,
        ebp = 56,
        rsi = 64,
        esi = 64,
        si = 64,
        sil = 64,
        sih = 65,
        rdi = 72,
        edi = 72,
        di = 72,
        dil = 72,
        dih = 73,
        r8 = 80,
        r8d = 80,
        r8w = 80,
        r8b = 80,
        r9 = 88,
        r9d = 88,
        r9w = 88,
        r9b = 88,
        r10 = 96,
        r10d = 96,
        r10w = 96,
        r10b = 96,
        r11 = 104,
        r11d = 104,
        r11w = 104,
        r11b = 104,
        r12 = 112,
        r12d = 112,
        r12w = 112,
        r12b = 112,
        r13 = 120,
        r13d = 120,
        r13w = 120,
        r13b = 120,
        r14 = 128,
        r14d = 128,
        r14w = 128,
        r14b = 128,
        r15 = 136,
        r15d = 136,
        r15w = 136,
        r15b = 136,
        cc_op = 144,
        cc_dep1 = 152,
        cc_dep2 = 160,
        cc_ndep = 168,
        d = 176,
        dflag = 176,
        rip = 184,
        ip = 184,
        pc = 184,
        ac = 192,
        acflag = 192,
        id = 200,
        idflag = 200,
        fs = 208,
        fs_const = 208,
        sseround = 216,
        ymm0 = 224,
        xmm0 = 224,
        ymm1 = 256,
        xmm1 = 256,
        ymm2 = 288,
        xmm2 = 288,
        ymm3 = 320,
        xmm3 = 320,
        ymm4 = 352,
        xmm4 = 352,
        ymm5 = 384,
        xmm5 = 384,
        ymm6 = 416,
        xmm6 = 416,
        ymm7 = 448,
        xmm7 = 448,
        ymm8 = 480,
        xmm8 = 480,
        ymm9 = 512,
        xmm9 = 512,
        ymm10 = 544,
        xmm10 = 544,
        ymm11 = 576,
        xmm11 = 576,
        ymm12 = 608,
        xmm12 = 608,
        ymm13 = 640,
        xmm13 = 640,
        ymm14 = 672,
        xmm14 = 672,
        ymm15 = 704,
        xmm15 = 704,
        ymm16 = 736,
        xmm16 = 736,
        ftop = 768,
        fpreg = 776,
        fpu_regs = 776,
        mm0 = 776,
        mm1 = 784,
        mm2 = 792,
        mm3 = 800,
        mm4 = 808,
        mm5 = 816,
        mm6 = 824,
        mm7 = 832,
        fptag = 840,
        fpu_tags = 840,
        fpround = 848,
        fc3210 = 856,
        emnote = 864,
        cmstart = 872,
        cmlen = 880,
        nraddr = 888,
        gs = 904,
        gs_const = 904,
        ip_at_syscall = 912
    }AMD64_IR_OFFSET;


}



namespace AMD64_IR_SIZE {
    typedef enum :unsigned int {
        rax = 8,
        eax = 4,
        ax = 2,
        al = 1,
        ah = 1,
        rcx = 8,
        ecx = 4,
        cx = 2,
        cl = 1,
        ch = 1,
        rdx = 8,
        edx = 4,
        dx = 2,
        dl = 1,
        dh = 1,
        rbx = 8,
        ebx = 4,
        bx = 2,
        bl = 1,
        bh = 1,
        rsp = 8,
        sp = 8,
        esp = 4,
        rbp = 8,
        bp = 8,
        ebp = 4,
        rsi = 8,
        esi = 4,
        si = 2,
        sil = 1,
        sih = 1,
        rdi = 8,
        edi = 4,
        di = 2,
        dil = 1,
        dih = 1,
        r8 = 8,
        r8d = 4,
        r8w = 2,
        r8b = 1,
        r9 = 8,
        r9d = 4,
        r9w = 2,
        r9b = 1,
        r10 = 8,
        r10d = 4,
        r10w = 2,
        r10b = 1,
        r11 = 8,
        r11d = 4,
        r11w = 2,
        r11b = 1,
        r12 = 8,
        r12d = 4,
        r12w = 2,
        r12b = 1,
        r13 = 8,
        r13d = 4,
        r13w = 2,
        r13b = 1,
        r14 = 8,
        r14d = 4,
        r14w = 2,
        r14b = 1,
        r15 = 8,
        r15d = 4,
        r15w = 2,
        r15b = 1,
        cc_op = 8,
        cc_dep1 = 8,
        cc_dep2 = 8,
        cc_ndep = 8,
        d = 8,
        dflag = 8,
        rip = 8,
        ip = 8,
        pc = 8,
        ac = 8,
        acflag = 8,
        id = 8,
        idflag = 8,
        fs = 8,
        fs_const = 8,
        sseround = 8,
        ymm0 = 32,
        xmm0 = 16,
        ymm1 = 32,
        xmm1 = 16,
        ymm2 = 32,
        xmm2 = 16,
        ymm3 = 32,
        xmm3 = 16,
        ymm4 = 32,
        xmm4 = 16,
        ymm5 = 32,
        xmm5 = 16,
        ymm6 = 32,
        xmm6 = 16,
        ymm7 = 32,
        xmm7 = 16,
        ymm8 = 32,
        xmm8 = 16,
        ymm9 = 32,
        xmm9 = 16,
        ymm10 = 32,
        xmm10 = 16,
        ymm11 = 32,
        xmm11 = 16,
        ymm12 = 32,
        xmm12 = 16,
        ymm13 = 32,
        xmm13 = 16,
        ymm14 = 32,
        xmm14 = 16,
        ymm15 = 32,
        xmm15 = 16,
        ymm16 = 32,
        xmm16 = 16,
        ftop = 4,
        fpreg = 64,
        fpu_regs = 64,
        mm0 = 8,
        mm1 = 8,
        mm2 = 8,
        mm3 = 8,
        mm4 = 8,
        mm5 = 8,
        mm6 = 8,
        mm7 = 8,
        fptag = 8,
        fpu_tags = 8,
        fpround = 8,
        fc3210 = 8,
        emnote = 4,
        cmstart = 8,
        cmlen = 8,
        nraddr = 8,
        gs = 8,
        gs_const = 8,
        ip_at_syscall = 8
    }AMD64_IR_SIZE;
}


#endif // HEADER_H

