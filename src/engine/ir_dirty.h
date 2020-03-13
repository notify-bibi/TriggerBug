#ifndef _IRDirty_H_
#define _IRDirty_H_
typedef struct _DirtyCtx* DirtyCtx;
#include "engine/state_class.h"
#include <initializer_list>
template<typename ADDR> DirtyCtx dirty_context(TR::State<ADDR>* s);
template<typename ADDR> Addr64 dirty_get_gsptr(DirtyCtx dctx);
template<typename ADDR> void dirty_context_del(DirtyCtx);
template<typename ADDR> void dirty_run(DirtyCtx dctx, IRDirty* dirty);
template<typename ADDR> void dirty_ccall(DirtyCtx dctx, IRCallee* cee, IRExpr** args);
template<typename ADDR> void dirty_call_np(DirtyCtx dctx, const HChar* name, void* func, const std::initializer_list<Vns>& parms);
template<typename ADDR> Vns dirty_result(DirtyCtx dctx, IRType rty);

#endif //_IRDirty_H_