#ifndef TR_EXCEPTION_H
#define TR_EXCEPTION_H


#include "engine/engine.h"

unsigned int TRCurrentThreadId();
const char* constStrIRJumpKind(IRJumpKind kind);

//Exception
namespace Expt {
    class GuestMemReadErr;
    class GuestMemWriteErr;
    class SolverNoSolution;
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
        ExceptionBase(ExceptionTag t);
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
        GuestMem(char const* msg, Addr64 gaddr, ExceptionTag err);
        virtual Addr64 addr() const override { return m_gaddr; }
    };

    class GuestMemReadErr :public GuestMem {
    public:
        GuestMemReadErr(char const* msg, Addr64 gaddr) :GuestMem(msg, gaddr, GuestMem_read_err) {}
        std::string msg() const override;
    };

    class GuestMemWriteErr :public GuestMem {
    public:
        GuestMemWriteErr(char const* msg, Addr64 gaddr) :GuestMem(msg, gaddr, GuestMem_write_err) {}
        std::string msg() const override;
    };

    class SolverNoSolution :public ExceptionBase {
        z3::solver& m_solver;
        const char* m_msg;
    public:
        SolverNoSolution(char const* msg, z3::solver& solver);
        std::string msg() const override;
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
        IRfailureExit(char* msg);
        IRfailureExit(
            const HChar* expr, const HChar* file, Int line, const HChar* fn
        );

        IRfailureExit(
            const HChar* file, Int line, const HChar* expr
        );

        std::string msg() const override;
    };


    class RuntimeIrSig :public ExceptionBase {
        Addr64 m_sig_addr;
        IRJumpKind m_jk;
    public:
        RuntimeIrSig(Addr64 a, IRJumpKind k);
        std::string msg() const override;
        virtual IRJumpKind jkd() const override { return m_jk; }
    };
};


inline std::ostream& operator << (std::ostream& out, const Expt::ExceptionBase& e) { return out << e.msg(); }


#define VPANIC(...) { throw Expt::IRfailureExit(__FILE__ ,__LINE__, __VA_ARGS__); }
//#define vpanic(...) { throw Expt::IRfailureExit(__FILE__ ,__LINE__, __VA_ARGS__); }

#if defined(_DEBUG)
#undef dassert
#define dassert(xexpr)                                           \
  ((void) (LIKELY(xexpr) ? 0 :                                        \
           (throw Expt::IRfailureExit (#xexpr,                            \
                             __FILE__, __LINE__,                \
                             __PRETTY_FUNCTION__), 0)))
#else
#define dassert(...) 
#endif // _DEBUG

#if !defined(RELEASE_OFFICIALLY)||defined(_DEBUG)
#define vassert(xexpr)                                           \
  ((void) (LIKELY(xexpr) ? 0 :                                         \
           (throw Expt::IRfailureExit (#xexpr,                             \
                             __FILE__, __LINE__,                 \
                             __PRETTY_FUNCTION__), 0)))
#else
#define vassert(...) 
#endif



#endif // TR_EXCEPTION_H