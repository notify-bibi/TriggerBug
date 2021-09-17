#ifndef TR_IR_OPT_HEADER
#define TR_IR_OPT_HEADER

extern "C" {
    #include <libvex_ir.h>
};

#include <cstdarg>
#include <stdio.h>
#include "instopt/engine/trException.h"
#include "spdlog/logger.h"

class ppIR {
    std::string m_str;
    std::shared_ptr<spdlog::logger> m_logger;
    spdlog::level::level_enum m_leve;

public:
    ppIR(std::shared_ptr<spdlog::logger> log, spdlog::level::level_enum leve) : m_logger(log), m_leve(leve) { }
    ppIR(std::shared_ptr<spdlog::logger> log) : ppIR(log, spdlog::level::debug) {}
    ~ppIR();
    inline std::string str()const { return m_str; };
    UInt vex_printf(const HChar* format, ...);

    void ppIRType(IRType ty);

    void ppIRConst(const IRConst* con);

    void ppIRCallee(const IRCallee* ce);

    void ppIRRegArray(const IRRegArray* arr);

    void ppIRTemp(IRTemp tmp);

    void ppIROp(IROp op);

    void ppIRExpr(const IRExpr* e);

    void ppIREffect(IREffect fx);

    void ppIRDirty(const IRDirty* d);

    void ppIRCAS(const IRCAS* cas);

    void ppIRPutI(const IRPutI* puti);

    void ppIRStoreG(const IRStoreG* sg);

    void ppIRLoadGOp(IRLoadGOp cvt);

    void ppIRLoadG(const IRLoadG* lg);

    void ppIRJumpKind(IRJumpKind kind);

    void ppIRMBusEvent(IRMBusEvent event);

    void ppIRStmt(const IRStmt* s);

    void ppIRTypeEnv(const IRTypeEnv* env);

    void ppIRSB(const IRSB* bb);


};

#endif // !TR_IR_OPT_HEADER
