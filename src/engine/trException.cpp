#include "engine/trException.h"


/*！！！！在这里下个断！！！！*/
/*！！！！add a backpoint here！！！！*/

Expt::ExceptionBase::ExceptionBase(ExceptionTag t) :m_errorId(t) {
    //错误过滤器 error filter
    ExceptionTag dbg;
    switch (t) {
    case GuestMem_read_err: dbg = t; break;
    case GuestMem_write_err: dbg = t; break;
    case GuestRuntime_exception: dbg = t; break;
    case IR_failure_exit: dbg = t; break;
    case Solver_no_solution: dbg = t; break;
    }
}


Expt::RuntimeIrSig::RuntimeIrSig(Addr64 a, IRJumpKind k) :ExceptionBase(GuestRuntime_exception), m_sig_addr(a), m_jk(k) {}

std::string Expt::RuntimeIrSig::msg() const {
    assert(m_errorId == GuestRuntime_exception);
    char buffer[50];
    snprintf(buffer, 50, "Guest : Sig(%s) at (%llu) :::  ", constStrIRJumpKind(m_jk), m_sig_addr);
    std::string ret;
    return ret.assign(buffer);
}

Expt::IRfailureExit::IRfailureExit(const char* msg) :ExceptionBase(IR_failure_exit),
    m_thread_id(TRCurrentThreadId()),
    m_error_message(msg),
    m_file(nullptr),
    m_line(0),
    m_expr(nullptr),
    m_fn(nullptr)
{
}

Expt::IRfailureExit::IRfailureExit(const HChar* expr, const HChar* file, Int line, const HChar* fn) :ExceptionBase(IR_failure_exit),
m_thread_id(TRCurrentThreadId()), m_file(file), m_line(line), m_expr(expr), m_fn(fn)
{
}

Expt::IRfailureExit::IRfailureExit(const HChar* file, Int line, const HChar* expr) : ExceptionBase(IR_failure_exit),
m_thread_id(TRCurrentThreadId()), m_file(file), m_line(line), m_expr(expr), m_fn(nullptr)
{
}

std::string Expt::IRfailureExit::msg() const {
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

Expt::SolverNoSolution::SolverNoSolution(char const* msg, z3::solver& solver) :ExceptionBase(Solver_no_solution), m_solver(solver), m_msg(msg) {}

 std::string Expt::SolverNoSolution::msg() const {
    assert(m_errorId == Solver_no_solution);
    return std::string("Solver no solution ::: ") + m_msg + "\nsolver's assertions:\n" +
        Z3_solver_to_string(m_solver.ctx(), m_solver);
}

 std::string Expt::GuestMemWriteErr::msg() const {
    assert(m_errorId == GuestMem_write_err);
    char buffer[50];
    snprintf(buffer, 50, "Gest : mem write addr(%llu) :::  ", m_gaddr);
    std::string ret;
    return ret.assign(buffer) + m_msg;
}

 std::string Expt::GuestMemReadErr::msg() const {
    assert(m_errorId == GuestMem_read_err);
    char buffer[50];
    snprintf(buffer, 50, "Gest : mem read addr(%llu) :::  ", m_gaddr);
    std::string ret;
    return ret.assign(buffer) + m_msg;
}

Expt::GuestMem::GuestMem(char const* msg, Addr64 gaddr, ExceptionTag err) :ExceptionBase(err),
    m_gaddr(gaddr), m_msg(msg) {
}
