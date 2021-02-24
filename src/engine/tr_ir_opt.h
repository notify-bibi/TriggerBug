#ifndef TR_IR_OPT_HEADER
#define TR_IR_OPT_HEADER

extern "C" {
    #include <libvex_ir.h>
};

#include <cstdarg>
#include <stdio.h>
#include "engine/trException.h"

class ppIR {

    HChar myprintf_buf[1000];
    Int   n_myprintf_buf;

public:
    ppIR() { n_myprintf_buf = 0; };

    inline const HChar* c_str() { return myprintf_buf; }
    inline std::string pop() { return myprintf_buf; }


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
