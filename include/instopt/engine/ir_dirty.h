#ifndef _IRDirty_H_
#define _IRDirty_H_
typedef struct _DirtyCtx* DirtyCtx;

#define MAX_GUEST_DIRTY_CALL_PARARM_NUM 15

#include "instopt/engine/state_explorer.h"
#include <initializer_list>
DirtyCtx dirty_context(TR::State* s);
Addr64 dirty_get_gsptr(DirtyCtx dctx);
void dirty_context_del(DirtyCtx);
void dirty_run(DirtyCtx dctx, const IRDirty* dirty);
void dirty_ccall(DirtyCtx dctx, const IRCallee* cee, IRExpr** const args);
void dirty_call_np(DirtyCtx dctx, const HChar* name, void* func, const std::initializer_list<rsval<Addr64>>& parms); // parms 是模拟host函数的参数，所以是64bits
sv::tval dirty_result(DirtyCtx dctx, IRType rty);

#endif //_IRDirty_H_