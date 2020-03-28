#ifndef _TR_head
#define _TR_head
#define _SILENCE_STDEXT_HASH_DEPRECATION_WARNINGS
#include <hash_map>
#include <intrin.h>    //(include immintrin.h)
#include <iostream>
#include <fstream>
#include <sstream>
#include <tuple>
#include <string>
#include <future>
#include <functional>
#include <iomanip>

#include "z3++.h"
#include "engine/ir_guest_defs.h"
#include "thread_pool/thread_pool.h"
#include "engine/trException.h"

//��������ûbug�˾�ȡ��ע�ͣ��ӿ��ٶ�
//#define RELEASE_OFFICIALLY

//���пͻ����Ĵ�����ir�����󳤶ȡ�����>=100
#define REGISTER_LEN 0x800

//100������ͻ���ָ������Ҫ����� IR temp index������>=400
#define MAX_IRTEMP 800

//ÿ����������ҳ����astʱ��ʹ��hash����ÿһ��ast;����ʹ��Z3_ast[0x1000];ǰ�ߺķ�С���ٶ���΢�������߷�֮
#define USE_HASH_AST_MANAGER

//copy one write дʱ���ƣ��ٶȿ죬Ĭ�ϲ��ر�
//#define CLOSECNW

//��ҳ����ast�Ϳ���һҳ�������ʹ�ø�ҳ��дʱ�ٸ���(�����ٶȿ�)
//#define USECNWNOAST

//��������ƽ̨�ܹ�
#define HOSTARCH VexArchAMD64

extern "C" void vex_assert_fail(const HChar * expr, const HChar * file, Int line, const HChar * fn);
extern "C" unsigned int vex_printf(const HChar * format, ...);
extern "C" void vpanic(const HChar * str);
unsigned int IRConstTag2nb(IRConstTag t);
unsigned int ty2length(IRType ty);
unsigned int ty2bit(IRType ty);
IRType       length2ty(UShort bit);
void         tAMD64REGS(int offset, int length);

#define __i386__
#define TESTCODE(code)                                                                                                  \
{                                                                                                                       \
    LARGE_INTEGER   freq = { 0 };                                                                                       \
    LARGE_INTEGER   beginPerformanceCount = { 0 };                                                                      \
    LARGE_INTEGER   closePerformanceCount = { 0 };                                                                      \
    QueryPerformanceFrequency(&freq);                                                                                   \
    QueryPerformanceCounter(&beginPerformanceCount);                                                                    \
    {   code    }                                                                                                       \
    QueryPerformanceCounter(&closePerformanceCount);                                                                    \
    double delta_seconds = (double)(closePerformanceCount.QuadPart - beginPerformanceCount.QuadPart) / freq.QuadPart;   \
    printf("%s line:%d spend %lf \n",__FILE__, __LINE__, delta_seconds);                                                \
}


#define ALIGN(Value,size) ((Value) & ~((size) - 1))
#define Z3_Get_Ref(exp) (((int*)((Z3_ast)((exp))))[2])
#define MMEMPTY _mm_empty() //x87����


#ifdef _MSC_VER
#define NORETURN __declspec(noreturn)
#else
#define NORETURN __attribute__ ((noreturn))
#endif


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
        //z3_translate�������̰߳�ȫ�ģ�target_ctx��ͬ��ctx��ͬ���ж��̲߳���Ҳ��bug��Ϊ��дʱ�������һ����
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


//ע��intel���������ĸ����ĸ�һ�µ�switch case���Զ�ʹ��if else�ṹ��������switchЧ�ʵ���




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


#endif _TR_head