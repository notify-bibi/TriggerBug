#ifndef _TR_head
#define _TR_head

// std::aligned_storage
#define _DISABLE_EXTENDED_ALIGNED_STORAGE  

// (4) return 0b000[1111] ull  (>=64) -1ull
#define fastMask(nb) ((((int)(nb)) >= 64)? (ULong)-1ll :((1ull << ((int)(nb))) - 1))

// (4) return 0b..1111[0000] ull  (>=64) 0ull
#define fastMaskReverse(nb) (~fastMask(nb))

// (4) return 0b001[1111] ull  (>=63) -1ull
#define fastMaskI1(nb) fastMask(((nb)+1))

// (4) return 0b..11110[0000] ull  (>=63) 0ull
#define fastMaskI1Reverse(nb) (~fastMaskI1(nb))

// nb => [0, 63]
// (0bhhhh000, 3) result 0bhhhh
// (0bhhhhLLL, 3) result 0bhhhh + 1
#define ALLOC_ALIGN_BIT(v, nb)  ((((v) + ((1ull<<(nb))-1))) >> (nb))

// nb => [0, 63]
// (0bhhhLLL, 3) result 0bhhh000
#define ALIGN_BIT(v, nb) ((v) & -(1ull<<(nb)))

// (0bhhhLLL, 0b1000) result 0bhhh000
#define ALIGN(v, size) ((v) & ~((size) - 1))

//注：高优化下编译器对四个及四个一下的switch case会自动使用if else结构。勿喷用switch效率低下

#if 0 // building with MSVC
# define LIKELY(x)          (x)
# define UNLIKELY(x)        (x)
# define CAST_TO_TYPEOF(x)  /**/
#else
# define LIKELY(x)          (__builtin_expect((bool)(x), 1))
# define UNLIKELY(x)        (__builtin_expect((bool)(x), 0))
# define CAST_TO_TYPEOF(x)  (__typeof__(x))
#endif // defined(_MSC_VER)

// rea is real address
#define dirty2rea(addr) ((ULong)(addr))|(1ull<<63)
#define rea2dirty(addr) ((ULong)(addr))&(~(1ull<<63))

//#include <mmintrin.h>  //SSE(include mmintrin.h)
//#include <xmmintrin.h> //SSE2(include xmmintrin.h)
//#include <emmintrin.h> //SSE3(include emmintrin.h)
//#include <pmmintrin.h> //SSSE3(include pmmintrin.h)
//#include <tmmintrin.h> //SSE4.1(include tmmintrin.h)
//#include <smmintrin.h> //SSE4.2(include smmintrin.h)
//#include <nmmintrin.h> //AES(include nmmintrin.h)
//#include <wmmintrin.h> //AVX(include wmmintrin.h)
#include <immintrin.h> //(include immintrin.h)





#if defined(_MSC_VER)
 /* Microsoft C/C++-compatible compiler */
#elif defined(__GNUC__) && !defined(__llvm__) && (!defined(__INTEL_COMPILER)) && (defined(__x86_64__))
 /* GCC-compatible compiler, targeting x86/x86-64 */
#define REAL_GCC   __GNUC__ // probably
#elif defined(__GNUC__) && !defined(__llvm__) && (defined(__INTEL_COMPILER)) && (defined(__x86_64__))
/* INTEL COMPILER */
#elif defined(__llvm__) && (defined(__x86_64__))
/* clang */
#else
#error "???"
#endif


#ifdef _MSC_VER
#define NORETURN __declspec(noreturn)
#else
#define NORETURN __attribute__ ((noreturn))
#endif


#if defined(_MSC_VER)
#include <intrin.h>
//#include <hash_map>
//#define HASH_MAP std::hash_map
#include <unordered_map>
#define HASH_MAP std::unordered_map
#define FAILD_ASSERT(false_any_cond, msg) static_assert(false, msg);

#else
#include <x86intrin.h>
#include <unordered_map>
#define HASH_MAP std::unordered_map
template <class...> constexpr std::false_type always_false{};
//#define FAILD_ASSERT(any_cond, msg) static_assert(always_false<any_cond>, msg);
#define FAILD_ASSERT(false_any_cond, msg) static_assert(false, msg); // if dont support please use -fdelayed-template-parsing
#define sprintf_s snprintf
#endif





#include <iostream>
#include <fstream>
#include <sstream>
#include <tuple>
#include <string>
#include <future>
#include <functional>
#include <iomanip>
#include <climits>
#include "z3++.h"
#include "engine/ir_guest_defs.h"
#include "thread_pool/thread_pool.h"
#include "engine/trException.h"

//觉得引擎没bug了就取消注释，加快速度
//#define RELEASE_OFFICIALLY

//所有客户机寄存器的ir层的最大长度。建议>=100
#define REGISTER_LEN 0x800

//任意基本快所需 IR temp 连续块大小，数量无限制
#define MAX_IRTEMP 0x80

//每个虚拟物理页存在ast时，使用hash保存每一个ast;否则使用Z3_ast[0x1000];前者耗费小，速度稍微慢，后者反之
#define USE_HASH_AST_MANAGER

//copy one write 写时复制，速度快，默认不关闭
//#define CLOSECNW

//父页存在ast就拷贝一页；否则就使用父页，写时再复制(后者速度快)
//#define USECNWNOAST

//宿主机的平台架构
#define HOSTARCH VexArchAMD64

extern "C" NORETURN void vex_assert_fail(const HChar * expr, const HChar * file, Int line, const HChar * fn);
extern "C" unsigned int vex_printf(const HChar * format, ...);
extern "C" NORETURN void vpanic(const HChar * str);
unsigned int IRConstTag2nb(IRConstTag t);
unsigned int ty2length(IRType ty);
unsigned int ty2bit(IRType ty);
IRType       length2ty(UShort bit);

#define TESTCODE(code) \
{                      \
    clock_t start;     \
    start = clock();   \
    {code; }           \
    printf("%s line:%d spend %lf \n",\
               __FILE__, __LINE__, \
               (double)(clock() - start) / CLOCKS_PER_SEC);\
}


#define Z3_Get_Ref(exp) (((int*)((Z3_ast)((exp))))[2])
#define MMEMPTY _mm_empty() //x87浮点



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
#define SET16(addr,fromaddr) _mm_storeu_si128(  *(__m128i_u*)((addr))), GET16(fromaddr))
#define SET32(addr,fromaddr) _mm256_storeu_si256(*(__m256i_u*)((addr)), GET32(fromaddr))

#define GET1(addr) (*(UChar*)((addr))) 
#define GET2(addr) (*(UShort*)((addr)))
#define GET4(addr) (*(UInt*)((addr)))
#define GET8(addr) (*(ULong*)((addr)))
#define GET16(addr) _mm_loadu_si128((__m128i_u*)((addr)))
#define GET32(addr) _mm256_loadu_si256((__m256i_u*)((addr)))


#define GETS1(addr) (*(Char*)((addr))) 
#define GETS2(addr) (*(Short*)((addr)))
#define GETS4(addr) (*(Int*)((addr)))
#define GETS8(addr) (*(Long*)((addr)))
#define GETS16(addr) GET16((addr))
#define GETS32(addr) GET32((addr))

#define MV1(addr,fromaddr) *(UChar*)((addr))=(*(UChar*)((fromaddr))) 
#define MV2(addr,fromaddr) *(UShort*)((addr))=(*(UShort*)((fromaddr)))
#define MV4(addr,fromaddr) *(UInt*)((addr))=(*(UInt*)((fromaddr)))
#define MV8(addr,fromaddr) *(ULong*)((addr))=(*(ULong*)((fromaddr)))
#define MV16(addr,fromaddr) SET16(addr, fromaddr)
#define MV32(addr,fromaddr) SET32(addr, fromaddr)


//class spin_mutex {
//    std::atomic<bool> flag = ATOMIC_VAR_INIT(false);
//public:
//    spin_mutex() = default;
//    spin_mutex(const spin_mutex&) = delete;
//    spin_mutex& operator= (const spin_mutex&) = delete;
//    void lock() {
//        bool expected = false;
//        while (!flag.compare_exchange_strong(expected, true))
//            expected = false;
//    }
//    void unlock() {
//        flag.store(false);
//    }
//};


class spin_mutex :std::mutex {
    std::atomic<bool> flag = ATOMIC_VAR_INIT(false);
public:
    spin_mutex() = default;
    spin_mutex(const spin_mutex&) = delete;
    spin_mutex& operator= (const spin_mutex&) = delete;
    inline void lock() {
        std::mutex::lock();
    }
    inline void unlock() {
        std::mutex::unlock();
    }
};

class spin_unique_lock {
    spin_mutex& m_mutex;
public:
    spin_unique_lock(const spin_unique_lock&) = delete;
    spin_unique_lock& operator= (const spin_unique_lock&) = delete;
    inline spin_unique_lock(spin_mutex& m) :m_mutex(m) { m_mutex.lock(); };
    inline ~spin_unique_lock() { m_mutex.unlock(); };
};

namespace z3 {
    class vcontext :public context {
        //z3_translate并不是线程安全的，target_ctx不同，ctx相同进行多线程并发也会bug。为了写时复制添加一个锁
        spin_mutex translate_mutex;
    public:

        inline vcontext() :context() { }
        inline spin_mutex& getLock() { return translate_mutex; };
        inline operator spin_mutex& () { return translate_mutex; };
        inline bool operator == (Z3_context b) const { return this->operator Z3_context() == b; };
        inline bool operator == (context const& b) const { return this->operator Z3_context() == (Z3_context)b; };
        inline bool operator == (vcontext const& b) const { return this->operator Z3_context() == (Z3_context)b; };
    };
}


struct no_inc {};


 
static inline bool clzll(int& r, unsigned long long v) { if (v == 0) return false; r = __builtin_clzll(v); return true; };
static inline bool clz(int& r, unsigned int v) { if (v == 0) return false; r = __builtin_clz(v); return true; };

static inline bool ctzll(int& r, unsigned long long v) { if (v == 0) return false; r = __builtin_ctzll(v); return true; };
static inline bool ctz(int& r, unsigned int v) { if (v == 0) return false; r = __builtin_ctz(v); return true; };


//inline unsigned short mscv_tid2temp() {
//    UChar index;
//    __asm__(\
//        "movq %%gs:0x30, %%rax ;\n\t"\
//        "movl 0x48(%%rax),%%eax;\n\t"\
//        "movq %[list],%%rdx;\n\t"\
//        "movb (%%rdx,%%rax,1),%%al;\n\t"\
//        "movl %%al,%[out];\n\t"\
//        : [out] "=r"(index) : [list] "r"(tid2temp) : "rax", "rdx");
//
//    return index;
//}


/*
 * Intel(R) AVX compiler intrinsic functions.
 */
typedef union __declspec(align(32)) _m256 {
    float m256_f32[8];
} _m256;

typedef struct __declspec(align(32)) _m256d {
    double m256d_f64[4];
} _m256d;

typedef union  __declspec(align(32)) _m256i {
    __int8              m256i_i8[32];
    __int16             m256i_i16[16];
    __int32             m256i_i32[8];
    __int64             m256i_i64[4];
    unsigned __int8     m256i_u8[32];
    unsigned __int16    m256i_u16[16];
    unsigned __int32    m256i_u32[8];
    unsigned __int64    m256i_u64[4];
} _m256i;

typedef union __declspec(align(16)) _m128i {
    __int8              m128i_i8[16];
    __int16             m128i_i16[8];
    __int32             m128i_i32[4];
    __int64             m128i_i64[2];
    unsigned __int8     m128i_u8[16];
    unsigned __int16    m128i_u16[8];
    unsigned __int32    m128i_u32[4];
    unsigned __int64    m128i_u64[2];
} _m128i;

typedef struct __declspec(align(16)) _m128d {
    double              m128d_f64[2];
} _m128d;


typedef union __declspec(align(16)) _m128 {
    float               m128_f32[4];
    unsigned __int64    m128_u64[2];
    __int8              m128_i8[16];
    __int16             m128_i16[8];
    __int32             m128_i32[4];
    __int64             m128_i64[2];
    unsigned __int8     m128_u8[16];
    unsigned __int16    m128_u16[8];
    unsigned __int32    m128_u32[4];
} _m128;



#define M256i(v) (*(_m256i*)(&v))
#define M256d(v) (*(_m256d*)(&v))
#define M256(v) (*(_m256*)(&v))

#define M128i(v) (*(_m128i*)(&v))
#define M128d(v) (*(_m128d*)(&v))
#define M128(v) (*(_m128*)(&v))


#endif // _TR_head
