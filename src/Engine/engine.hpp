#ifndef _TR_head
#define _TR_head
#define _SILENCE_STDEXT_HASH_DEPRECATION_WARNINGS
#include <hash_map>
#include <windows.h>
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
#include <exception>
#include <string>
#include <vector>
#include <queue>
#include <memory>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <future>
#include <functional>
#include <stdexcept>
#include <iomanip>
#include "api/c++/z3++.h"


#ifdef DLL_EXPORTS
#define DLLDEMO_API __declspec(dllexport)
#else
#define DLLDEMO_API __declspec(dllimport)
#endif

#define Py_LIMITED_API
#ifdef _DEBUG
#undef _DEBUG
#include <python\Python.h>
#define _DEBUG 1
#else
#include <python\Python.h>
#endif

//��������ûbug�˾�ȡ��ע�ͣ��ӿ��ٶ�
//#define RELEASE_OFFICIALLY

//���пͻ����Ĵ�����ir�����󳤶ȡ�����>=100
#define REGISTER_LEN 1000

//100������ͻ���ָ������Ҫ����� IR temp index������>=400
#define MAX_IRTEMP 400

//ÿ����������ҳ����astʱ��ʹ��hash����ÿһ��ast;����ʹ��Z3_ast[0x1000];ǰ�ߺķ�С���ٶ���΢�������߷�֮
#define USE_HASH_AST_MANAGER

//copy one write дʱ���ƣ��ٶȿ죬Ĭ�ϲ��ر�
//#define CLOSECNW

//��ҳ����ast�Ϳ���һҳ�������ʹ�ø�ҳ��дʱ�ٸ���(�����ٶȿ�)
//#define USECNWNOAST

//��������ƽ̨�ܹ�
#define HOSTARCH VexArchAMD64

#include "Engine/header.hpp"
#include "Engine/Thread_Pool/ThreadPool_CD.hpp"


class TRcontext :public z3::context {
    //z3_translate�������̰߳�ȫ�ģ�target_ctx��ͬ��ctx��ͬ���ж��̲߳���Ҳ��bug��Ϊ��дʱ�������һ����
    std::mutex translate_mutex;
public:
    
    inline TRcontext() :z3::context() { }
    inline std::mutex& getLock() { return translate_mutex; };
    inline operator std::mutex& () { return translate_mutex; };
    inline bool operator == (Z3_context b) const { return this->operator Z3_context() == b; };
    inline bool operator == (z3::context const& b) const { return this->operator Z3_context() == (Z3_context)b; };
    inline bool operator == (TRcontext const &b) const{ return this->operator Z3_context() == (Z3_context)b; };
};

//ע��intel���������ĸ����ĸ�һ�µ�switch case���Զ�ʹ��if else�ṹ��




//Exception
namespace Expt {
    typedef enum {
        //ģ���������
        GuestMem_read_err,
        GuestMem_write_err,
        //���bug
        /*
        Engine_memory_leak,
        Engine_memory_unmap_has_ref,
        Engine_memory_access_has_ref,
        */
        IR_failure_exit,
        //z3 solver �޽�
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
                return ret.assign(buffer) +
                    "file: " + m_file + "\n"
                    "line: " + tline + "\n"
                    "expr: " + m_expr + "\n"
                    "func: " + m_fn;
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

#include "Engine/functions/functions.hpp"

#endif _TR_head