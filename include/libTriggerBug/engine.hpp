#ifndef _TR_head
#define _TR_head
#define _SILENCE_STDEXT_HASH_DEPRECATION_WARNINGS
#include <hash_map>
#include <mmintrin.h>  //MMX
#include <xmmintrin.h> //SSE(include mmintrin.h)
#include <emmintrin.h> //SSE2(include xmmintrin.h)
#include <pmmintrin.h> //SSE3(include emmintrin.h)
#include <tmmintrin.h> //SSSE3(include pmmintrin.h)
#include <smmintrin.h> //SSE4.1(include tmmintrin.h)
#include <nmmintrin.h> //SSE4.2(include smmintrin.h)
#include <wmmintrin.h> //AES(include nmmintrin.h)
#include <immintrin.h> //AVX(include wmmintrin.h)
#include <intrin.h>    //(include immintrin.h)
#include <iostream>
#include <fstream>
#include <sstream>
#include <tuple>
#include <string>
#include <vector>
#include <queue>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <future>
#include <functional>
#include <iomanip>
#include "api/c++/z3++.h"
#include <windows.h>


//觉得引擎没bug了就取消注释，加快速度
//#define RELEASE_OFFICIALLY

//所有客户机寄存器的ir层的最大长度。建议>=100
#define REGISTER_LEN 1000

//100条任意客户机指令所需要的最大 IR temp index。建议>=400
#define MAX_IRTEMP 400

//每个虚拟物理页存在ast时，使用hash保存每一个ast;否则使用Z3_ast[0x1000];前者耗费小，速度稍微慢，后者反之
#define USE_HASH_AST_MANAGER

//copy one write 写时复制，速度快，默认不关闭
//#define CLOSECNW

//父页存在ast就拷贝一页；否则就使用父页，写时再复制(后者速度快)
//#define USECNWNOAST

//宿主机的平台架构
#define HOSTARCH VexArchAMD64

#include "engine/header.hpp"
#include "thread_pool/threadpool.h"


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


class TRcontext :public z3::context {
    //z3_translate并不是线程安全的，target_ctx不同，ctx相同进行多线程并发也会bug。为了写时复制添加一个锁
    spin_mutex translate_mutex;
public:
    
    inline TRcontext() :z3::context() { }
    inline spin_mutex& getLock() { return translate_mutex; };
    inline operator spin_mutex& () { return translate_mutex; };
    inline bool operator == (Z3_context b) const { return this->operator Z3_context() == b; };
    inline bool operator == (z3::context const& b) const { return this->operator Z3_context() == (Z3_context)b; };
    inline bool operator == (TRcontext const &b) const{ return this->operator Z3_context() == (Z3_context)b; };
};



//注：intel编译器对四个及四个一下的switch case会自动使用if else结构。




//Exception
namespace Expt {
    typedef enum {
        //模拟软件错误
        GuestMem_read_err,
        GuestMem_write_err,
        //设计bug
        /*
        Engine_memory_leak,
        Engine_memory_unmap_has_ref,
        Engine_memory_access_has_ref,
        */
        IR_failure_exit,
        //z3 solver 无解
        Solver_no_solution
        //
    }ExceptionTag;

    class ExceptionBase {
        friend class GuestMem;
        friend class GuestMemReadErr;
        friend class GuestMemWriteErr;
        friend class Solver_no_solution; 
        friend class SolverNoSolution;
        friend class IRfailureExit;
        ExceptionTag m_errorId;
        ExceptionBase(ExceptionTag t) :m_errorId(t) {}
    public:
        operator ExceptionTag() { return m_errorId; };
        std::string msg() const;
    };

    class GuestMem :public ExceptionBase {
        friend class GuestMemReadErr;
        friend class GuestMemWriteErr;
        Addr64 m_gaddr;
        std::string m_msg;
        GuestMem(char const* msg, Addr64 gaddr, ExceptionTag err) :ExceptionBase(err),
            m_msg(msg), m_gaddr(gaddr) {
        }
    };

    class GuestMemReadErr :public GuestMem {
    public:
        GuestMemReadErr(char const* msg, Addr64 gaddr) :GuestMem(msg, gaddr, GuestMem_read_err) {}
        std::string msg() const {
            assert(m_errorId == GuestMem_read_err);
            char buffer[50];
            snprintf(buffer, 50, "Gest : mem read addr(%p) :::  ", m_gaddr);
            std::string ret;
            return ret.assign(buffer) + m_msg ;
        }
    };

    class GuestMemWriteErr :public GuestMem {
    public:
        GuestMemWriteErr(char const* msg, Addr64 gaddr) :GuestMem(msg, gaddr, GuestMem_write_err) {}
        std::string msg() const {
            assert(m_errorId == GuestMem_write_err);
            char buffer[50];
            snprintf(buffer, 50, "Gest : mem write addr(%p) :::  ", m_gaddr);
            std::string ret;
            return ret.assign(buffer) + m_msg;
        }
    };

    class SolverNoSolution :public ExceptionBase {
        z3::solver& m_solver;
        const char * m_msg;
    public:
        SolverNoSolution(char const* msg, z3::solver& solver) :ExceptionBase(Solver_no_solution), m_msg(msg), m_solver(solver) {}
        std::string msg() const {
            assert(m_errorId == Solver_no_solution);
            return std::string("Solver no solution ::: ") + m_msg + "\nsolver's assertions:\n" +
                Z3_solver_to_string(m_solver.ctx(), m_solver);
        }
        operator z3::solver& () { return m_solver; };
    };

    // vapnic or vassert or dassert
    class IRfailureExit :public ExceptionBase {
        UInt m_thread_id;
        std::string m_error_message;
        const HChar* m_file;
        Int m_line;
        const HChar* m_expr;
        const HChar* m_fn;
    public:
        IRfailureExit(char* msg) :ExceptionBase(IR_failure_exit),
            m_thread_id(GetCurrentThreadId()),
            m_error_message(msg), m_expr(nullptr), m_file(nullptr), m_line(0), m_fn(nullptr)
        {
        }
        IRfailureExit(
            const HChar* expr, const HChar* file, Int line, const HChar* fn
        ) :ExceptionBase(IR_failure_exit),
            m_thread_id(GetCurrentThreadId()), m_expr(expr), m_file(file), m_line(line), m_fn(fn)
        {
        }

        IRfailureExit(
            const HChar* file, Int line, const HChar* expr
        ) :ExceptionBase(IR_failure_exit),
            m_thread_id(GetCurrentThreadId()), m_expr(expr), m_file(file), m_line(line), m_fn(nullptr)
        {
        }

        std::string msg() const {
            assert(m_errorId == IR_failure_exit);
            if (m_expr && m_file) {
                char buffer[50];
                char tline[10];
                snprintf(buffer, 50, "IRfailureExit ::: Thread id: %d\n", m_thread_id);
                snprintf(tline, 10, "%d", m_line);
                std::string ret;
                ret = ret.assign(buffer) +
                    "file: " + m_file + "\n"
                    "line: " + tline + "\n"
                    "expr: " + m_expr;
                if (m_fn) { return ret + "\n""func: " + m_fn; }
                return ret;
            }
            else {
                char buffer[50];
                snprintf(buffer, 50, "IRfailureExit ::: Thread id: %d\n", m_thread_id);
                return buffer + m_error_message;
            }
        }
    };
};

inline static std::ostream& operator<<(std::ostream& out, Expt::ExceptionBase const& e) { out << e.msg(); return out; }
inline static std::ostream& operator<<(std::ostream& out, Expt::GuestMemReadErr const& e) { out << e.msg(); return out; }
inline static std::ostream& operator<<(std::ostream& out, Expt::GuestMemWriteErr const& e) { out << e.msg(); return out; }
inline static std::ostream& operator<<(std::ostream& out, Expt::SolverNoSolution const& e) { out << e.msg(); return out; }
inline static std::ostream& operator<<(std::ostream& out, Expt::IRfailureExit const& e) { out << e.msg(); return out; }


#define VPANIC(...) { throw Expt::IRfailureExit(__FILE__ ,__LINE__, __VA_ARGS__); }
//#define vpanic(...) { throw Expt::IRfailureExit(__FILE__ ,__LINE__, __VA_ARGS__); }

#if defined(_DEBUG)
#undef dassert
#define dassert(xexpr)                                           \
  ((void) ((xexpr) ? 0 :                                        \
           (throw Expt::IRfailureExit (#xexpr,                            \
                             __FILE__, __LINE__,                \
                             __FUNCSIG__), 0)))
#else
#define dassert(...) 
#endif // _DEBUG

#if !defined(RELEASE_OFFICIALLY)||defined(_DEBUG)
#define vassert(xexpr)                                           \
  ((void) ((xexpr) ? 0 :                                         \
           (throw Expt::IRfailureExit (#xexpr,                             \
                             __FILE__, __LINE__,                 \
                             __FUNCSIG__), 0)))
#else
#define vassert(...) 
#endif

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

unsigned int IRConstTag2nb(IRConstTag t);
unsigned int ty2length(IRType ty);
unsigned int ty2bit(IRType ty);
IRType length2ty(UShort bit);
void tAMD64REGS(int offset, int length);


#endif _TR_head