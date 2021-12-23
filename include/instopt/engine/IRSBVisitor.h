#pragma once
#include "instopt/engine/vexStateHelper.h"
#include "instopt/tracer/BlockView.h"
#include 
template <template <typename> class Ptr, typename ImplClass,
          typename RetTy = void, class... ParamTys>
class IRSBVisitorVisitorBase {
    IRSBVisitorVisitorBase() {}

#define DISPATCH(NAME, CLASS)                                                  \
  return static_cast<ImplClass *>(this)->Visit##NAME(                          \
      static_cast<PTR(CLASS)>(S), std::forward<ParamTys>(P)...)

    virtual void visit_CCall(IRExpr* e) {
        Int i;
        for (i = 0; e->Iex.CCall.args[i]; i++)
            visitExpr(e->Iex.CCall.args[i]);
        return;
    }
    virtual void visit_ITE(IRExpr* e) {
        visitExpr(e->Iex.ITE.cond);
        visitExpr(e->Iex.ITE.iftrue);
        visitExpr(e->Iex.ITE.iffalse);
    }
    virtual void visit_Qop(IRExpr* e) {
        visitExpr(e->Iex.Qop.details->arg1);
        visitExpr(e->Iex.Qop.details->arg2);
        visitExpr(e->Iex.Qop.details->arg3);
        visitExpr(e->Iex.Qop.details->arg4);
    }
    virtual void visit_Triop(IRExpr* e) {
        visitExpr(e->Iex.Triop.details->arg1);
        visitExpr(e->Iex.Triop.details->arg2);
        visitExpr(e->Iex.Triop.details->arg3);
    }
    virtual void visit_Binop(IRExpr* e) {
        visitExpr(e->Iex.Binop.arg1);
        visitExpr(e->Iex.Binop.arg2);
    }
    virtual void visit_Unop(IRExpr* e) {
        visitExpr(e->Iex.Unop.arg);
    }
    virtual void visit_Load(IRExpr* e) {
        visitExpr(e->Iex.Load.addr);
    }
    virtual void visit_Get(IRExpr* e) {
        regGet(e->Iex.Get.offset, e->Iex.Get.ty);
    }
    virtual void visit_GetI(IRExpr* e) {
        IRRegArray* descr = e->Iex.GetI.descr;
        Int size = sizeofIRType(descr->elemTy);
        regGet(descr->base, descr->nElems * size);
        visitExpr(e->Iex.GetI.ix);
    }
    virtual void visit_RdTmp(IRExpr* e) {
    }
    virtual void visit_Const(IRExpr* e) {
    }
    void visitExpr(IRExpr* e) {
        switch (e->tag) {
#define IEX(IexName) case Iex_##IexName: { visit_##IexName(e); }
#include "instopt/tracer/IRSB.def"
#undef IEX
            return;
        default:
            VPANIC("visitExpr");
        }
    }
    virtual void regPut(Int offset, Int size) {

    }
    virtual void regGet(Int offset, IRType ty) {

    }



    virtual IRTypeEnv* getIRTypeEnv() = 0;
    virtual IRType typeOfIRExpr(IRTypeEnv* tyenv, IRExpr* e) { return ::typeOfIRExpr(tyenv, e); }

    virtual void visit_Put(IRStmt* st) {
        regPut(st->Ist.Put.offset,
            sizeofIRType(typeOfIRExpr(getIRTypeEnv(), st->Ist.Put.data)));
        visitExpr(st->Ist.Put.data);
    }
    virtual void visit_PutI(IRStmt* st) {
        IRPutI* puti;
        puti = st->Ist.PutI.details;
        IRRegArray* descr = puti->descr;
        regPut(descr->base,
            descr->nElems * sizeofIRType(descr->elemTy));
        visitExpr(puti->ix);
        visitExpr(puti->data);
    }
    virtual void visit_WrTmp(IRStmt* st) {
        visitExpr(st->Ist.WrTmp.data);
    }
    virtual void visit_Store(IRStmt* st) {
        visitExpr(st->Ist.Store.addr);
        visitExpr(st->Ist.Store.data);
    }
    virtual void visit_StoreG(IRStmt* st) {
        IRStoreG* sg;
        sg = st->Ist.StoreG.details;
        visitExpr(sg->addr);
        visitExpr(sg->data);
        visitExpr(sg->guard);
    }
    virtual void visit_LoadG(IRStmt* st) {
        IRLoadG* lg;
        lg = st->Ist.LoadG.details;
        visitExpr(lg->addr);
        visitExpr(lg->alt);
        visitExpr(lg->guard);
    }
    virtual void visit_CAS(IRStmt* st) {
        IRCAS* cas;
        cas = st->Ist.CAS.details;
        visitExpr(cas->addr);
        if (cas->expdHi)
            visitExpr(cas->expdHi);
        visitExpr(cas->expdLo);
        if (cas->dataHi)
            visitExpr(cas->dataHi);
        visitExpr(cas->dataLo);
    }
    virtual void visit_LLSC(IRStmt* st) {
        visitExpr(st->Ist.LLSC.addr);
        visitExpr(st->Ist.LLSC.storedata);
    }
    virtual void visit_Dirty(IRStmt* st) {
        Int i;
        IRDirty* d, * d2;
        d = st->Ist.Dirty.details;

        Int j;
        for (j = 0; j < d->nFxState; j++) {
            if (d->fxState[j].fx == Ifx_Modify || d->fxState[j].fx == Ifx_Write) {
                Int offset = d->fxState[i].offset;
                Int size = d->fxState[i].size;
                Int nRepeats = d->fxState[i].nRepeats;
                Int repeatLen = d->fxState[i].repeatLen;
                regPut(offset, nRepeats * repeatLen + size);
            }
        }

        d2 = emptyIRDirty();
        *d2 = *d;
        d2->args = shallowCopyIRExprVec(d2->args);
        if (d2->mFx != Ifx_None) {
            visitExpr(d2->mAddr);
        }
        else {
            vassert(d2->mAddr == NULL);
        }
        visitExpr(d2->guard);
        for (i = 0; d2->args[i]; i++) {
            IRExpr* arg = d2->args[i];
            if (LIKELY(!is_IRExpr_VECRET_or_GSPTR(arg)))
                visitExpr(arg);
        }
    }
    virtual void visit_NoOp(IRStmt* st) {
    }
    virtual void visit_MBE(IRStmt* st) {
    }
    virtual void visit_IMark(IRStmt* st) {
    }
    virtual void visit_AbiHint(IRStmt* st) {
        visitExpr(st->Ist.AbiHint.base);
        visitExpr(st->Ist.AbiHint.nia);
    }
    virtual void visit_Exit(IRStmt* st) {
        visitExpr(st->Ist.Exit.guard);
        if (st->Ist.Exit.jk == Ijk_Boring) {
            Addr next = st->Ist.Exit.dst->Ico.U64;
            if (st->Ist.Exit.dst->tag == Ico_U32)
                next = (UInt)next;
        }
    }

    virtual void visit(IRStmt* st) {
        switch (st->tag) {
#define IST(IstName) case Ist_##IstName: { visit_##IstName(st); }
#include "instopt/tracer/IRSB.def"
#undef IST
        default:
            VPANIC("flatten_Stmt");
        };
    }
    virtual void visitTyEnv(IRTypeEnv* tyenv) {};
    virtual void visitStmts(IRStmt** stmts,Int stmts_used) {
        Int i;
        for (i = 0; i < stmts_used; i++) {
            IRStmt* st = stmts[i];
            visit(st);
        }
    };
    virtual RetTy visitNext(IRExpr *next, IRJumpKind jumpkind, Int offsIP){};
    virtual RetTy visit(IRSB *irsb, ParamTys... P) {
        visitTyEnv(irsb->tyenv);
        visitStmts(irsb->stmts, irsb->stmts_used);
        visitNext(irsb->next, irsb->jumpkind, irsb->offsIP);
    }
};

// 高级反编译 人看
class AstBlock {
    typedef typename std::pair<Int, Int> key_value_pair_t;
    std::list<key_value_pair_t> m_param;  // regOffset size
    std::list<key_value_pair_t> m_result; // regOffset size

    typedef typename std::list<key_value_pair_t>::iterator list_iterator_t;
    irsb_chunk m_block;
    IRJumpKind m_jmpkind;

public:
    AstBlock(irsb_chunk irsb_chunk) : m_block(irsb_chunk) {
        IRSB* irsb = m_block->get_irsb();
        m_jmpkind = irsb->jumpkind;
    }
    typedef struct {
        Bool present;
        Int low;
        Int high;
    } Interval;

    //inline void update_interval(std::list<key_value_pair_t>& i, Int offset,
    //    Int size) {
    //    vassert(size > 0);
    //    Int lo2 = offset;
    //    Int hi2 = offset + size - 1;
    //    list_iterator_t it = i.begin();
    //    for (; it != i.end();) {
    //        Int lo = it->first;
    //        Int hi = it->second;
    //        // over
    //        if ((lo >= lo2 && lo <= hi2) || (lo2 >= lo && lo2 <= hi)) {
    //            if (lo > lo2)
    //                lo = lo2;
    //            if (hi < hi2)
    //                hi = hi2;
    //            it = i.erase(it);
    //            update_interval(i, lo, hi - lo + 1);
    //            return;
    //        }
    //        it++;
    //    }
    //    i.push_back(key_value_pair_t(lo2, hi2));
    //}

    virtual ~AstBlock() {}
};

template <typename ImplClass, typename RetTy = void, typename... ParamTys>
class IRSBVisitor : public IRSBVisitorVisitorBase<std::add_pointer, ImplClass,
                                                  RetTy, ParamTys...> {};
