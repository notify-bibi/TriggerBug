#ifndef _IRDirty_H_
#define _IRDirty_H_
typedef struct _DirtyCtx* DirtyCtx;
#include "State_class.hpp"
template<typename ADDR> DirtyCtx dirty_context(State<ADDR>* s);
template<typename ADDR> Addr64 dirty_get_gsptr(DirtyCtx dctx);
template<typename ADDR> void dirty_context_del(DirtyCtx);
template<typename ADDR> void dirty_run(DirtyCtx dctx, IRDirty* dirty);
template<typename ADDR> void dirty_ccall(DirtyCtx dctx, IRCallee* cee, IRExpr** args);
template<typename ADDR> Vns dirty_result(DirtyCtx dctx, IRType rty);
#endif //_IRDirty_H_