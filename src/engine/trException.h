#pragma once
#include "engine/engine.h"

unsigned int TRCurrentThreadId();
const char* constStrIRJumpKind(IRJumpKind kind);

//Exception
namespace Expt {
    class GuestMemReadErr;
    class GuestMemWriteErr;

    typedef enum {
        //模拟软件错误
        GuestMem_read_err,
        GuestMem_write_err,
        GuestRuntime_exception,
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
        friend class RuntimeIrSig;

        ExceptionTag m_errorId;
        /*！！！！在这里下个断！！！！*/
        /*！！！！add a backpoint here！！！！*/
        ExceptionBase(ExceptionTag t) :m_errorId(t) {}
    public:
        ExceptionTag errTag() const { return m_errorId; };
        virtual std::string msg() const { printf("GG"); exit(1); };
        virtual Addr64 addr() const { return 0; }
        virtual IRJumpKind jkd() const { return Ijk_INVALID; }
    };

    class GuestMem :public ExceptionBase {
        friend class GuestMemReadErr;
        friend class GuestMemWriteErr;
        Addr64 m_gaddr;
        std::string m_msg;
        GuestMem(char const* msg, Addr64 gaddr, ExceptionTag err) :ExceptionBase(err),
            m_msg(msg), m_gaddr(gaddr) {
        }
        virtual Addr64 addr() const override { return m_gaddr; }
    };

    class GuestMemReadErr :public GuestMem {
    public:
        GuestMemReadErr(char const* msg, Addr64 gaddr) :GuestMem(msg, gaddr, GuestMem_read_err) {}
        std::string msg() const override {
            assert(m_errorId == GuestMem_read_err);
            char buffer[50];
            snprintf(buffer, 50, "Gest : mem read addr(%p) :::  ", m_gaddr);
            std::string ret;
            return ret.assign(buffer) + m_msg;
        }
    };

    class GuestMemWriteErr :public GuestMem {
    public:
        GuestMemWriteErr(char const* msg, Addr64 gaddr) :GuestMem(msg, gaddr, GuestMem_write_err) {}
        std::string msg() const override {
            assert(m_errorId == GuestMem_write_err);
            char buffer[50];
            snprintf(buffer, 50, "Gest : mem write addr(%p) :::  ", m_gaddr);
            std::string ret;
            return ret.assign(buffer) + m_msg;
        }
    };

    class SolverNoSolution :public ExceptionBase {
        z3::solver& m_solver;
        const char* m_msg;
    public:
        SolverNoSolution(char const* msg, z3::solver& solver) :ExceptionBase(Solver_no_solution), m_msg(msg), m_solver(solver) {}
        std::string msg() const override {
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
            m_thread_id(TRCurrentThreadId()),
            m_error_message(msg),
            m_file(nullptr),
            m_line(0),
            m_expr(nullptr),
            m_fn(nullptr)
        {
        }
        IRfailureExit(
            const HChar* expr, const HChar* file, Int line, const HChar* fn
        ) :ExceptionBase(IR_failure_exit),
            m_thread_id(TRCurrentThreadId()), m_file(file), m_line(line), m_expr(expr), m_fn(fn)
        {
        }

        IRfailureExit(
            const HChar* file, Int line, const HChar* expr
        ) :ExceptionBase(IR_failure_exit),
            m_thread_id(TRCurrentThreadId()), m_file(file), m_line(line), m_expr(expr), m_fn(nullptr)
        {
        }

        std::string msg() const override {
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


    class RuntimeIrSig :public ExceptionBase {
        Addr64 m_sig_addr;
        IRJumpKind m_jk;
    public:
        RuntimeIrSig(Addr64 a, IRJumpKind k) :ExceptionBase(GuestRuntime_exception), m_sig_addr(a), m_jk(k) {}
        std::string msg() const override {
            assert(m_errorId == GuestRuntime_exception);
            char buffer[50];
            snprintf(buffer, 50, "Guest : Sig(%s) at (%p) :::  ", constStrIRJumpKind(m_jk), m_sig_addr);
            std::string ret;
            return ret.assign(buffer);
        }
        virtual IRJumpKind jkd() const override { return m_jk; }
    };
};


inline std::ostream& operator << (std::ostream& out, const Expt::ExceptionBase& e) { return out << e.msg(); }


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