#pragma once

extern "C" {
#include "libvex.h"
}
#include "llvm/ADT/Optional.h"
#include <type_traits>
namespace TR {
	template<typename InterpretClass>
	struct InterpretInfo {
		using ValTy = void*;
		using conValTy = const ValTy&;
		using IstRetTy = bool;
		using conIstRetTy = const IstRetTy&;
	};

	template<typename InterpretClass = void*, typename INFO = InterpretInfo<InterpretClass>>
	class InterpretIRSB {
		using ValTy = typename INFO::ValTy;
		using conValTy = typename INFO::conValTy;
		using IstRetTy = typename INFO::IstRetTy;
		using conIstRetTy = typename INFO::conIstRetTy;
		// using  INFO = struct InterpretInfo<InterpretClass >;

		static_assert(!std::is_reference<ValTy>::value, "dont be type&");
		static_assert(!std::is_reference<IstRetTy>::value, "dont be type&");
		InterpretIRSB() {}

		virtual void setTyEnv(const IRTypeEnv* tyenv) = 0;

		virtual IstRetTy regPut(Int offset, ValTy Val) = 0;
		virtual IstRetTy regPut(Int base, Int bias, ValTy ix, Int nElems, IRType elemTy, ValTy Val) = 0;
		virtual ValTy regGet(Int offset, IRType ty) const = 0;
		virtual ValTy regGet(Int base, Int bias, ValTy ix, Int nElems, IRType elemTy) const = 0;
		virtual IstRetTy memStore(ValTy addr, ValTy Val, Int size) = 0;
		virtual ValTy memLoad(ValTy addr, IRType ty, IREndness endess) const = 0;

		virtual ValTy Interpret_RdTmp(const IRExpr* e) const = 0;
		virtual ValTy Interpret_Const(const IRExpr* e) const = 0;
		virtual ValTy Interpret_CCall(const IRExpr* e) const = 0;
		virtual ValTy Interpret_GSPTR(const IRExpr* e) const = 0;
		virtual ValTy Interpret_VECRET(const IRExpr* e) const = 0;
		virtual ValTy Interpret_ITE(ValTy cond, ValTy iftrue, ValTy iffalse) const = 0;
		virtual ValTy Interpret_Qop(ValTy arg1, ValTy arg2, ValTy arg3, ValTy arg4) const = 0;
		virtual ValTy Interpret_Triop(ValTy arg1, ValTy arg2, ValTy arg3) const = 0;
		virtual ValTy Interpret_Binop(ValTy arg1, ValTy arg2) const = 0;
		virtual ValTy Interpret_Unop(ValTy arg1) const = 0;


		virtual IstRetTy Interpret_WrTmp(IRTemp tmp, ValTy Val) = 0;
		virtual IstRetTy Interpret_Store(ValTy addr, ValTy Val, IREndness end) = 0;
		virtual IstRetTy Interpret_StoreG(ValTy guard, ValTy addr, ValTy data, IREndness end) = 0;
		virtual IstRetTy Interpret_LoadG(IRTemp dst, ValTy guard, ValTy addr, ValTy alt, IRLoadGOp cvt, IREndness end) = 0;
		virtual IstRetTy Interpret_CAS(ValTy addr, ValTy expdLo, ValTy dataLo, const llvm::Optional<ValTy>& expdHi, const llvm::Optional<ValTy>& dataHi, IREndness end) = 0;
		virtual IstRetTy Interpret_LLSC(IRTemp result, ValTy addr, ValTy storedata, IREndness end) = 0;
		virtual IstRetTy Interpret_IMark(Addr addr, UInt len, UChar delta) = 0;
		virtual IstRetTy Interpret_AbiHint(ValTy base, ValTy nia) = 0;
		virtual IstRetTy Interpret_Exit(ValTy guard, IRJumpKind jk, Addr next, Int offsIP) = 0;
		virtual IstRetTy Interpret_MBE(IRMBusEvent event) = 0;
		virtual IstRetTy Interpret_Dirty(const IRStmt* st) = 0;

		virtual ValTy Interpret_ITE(const IRExpr* e) const {
			ValTy cond = InterpretExpr(e->Iex.ITE.cond);
			ValTy iftrue = InterpretExpr(e->Iex.ITE.iftrue);
			ValTy iffalse = InterpretExpr(e->Iex.ITE.iffalse);
			return Interpret_ITE(cond, iftrue, iffalse);
		}
		virtual ValTy Interpret_Qop(const IRExpr* e) const {
			ValTy arg1 = InterpretExpr(e->Iex.Qop.details->arg1);
			ValTy arg2 = InterpretExpr(e->Iex.Qop.details->arg2);
			ValTy arg3 = InterpretExpr(e->Iex.Qop.details->arg3);
			ValTy arg4 = InterpretExpr(e->Iex.Qop.details->arg4);
			return Interpret_Qop(arg1, arg2, arg3, arg4);
		}
		virtual ValTy Interpret_Triop(const IRExpr* e) const {
			ValTy arg1 = InterpretExpr(e->Iex.Triop.details->arg1);
			ValTy arg2 = InterpretExpr(e->Iex.Triop.details->arg2);
			ValTy arg3 = InterpretExpr(e->Iex.Triop.details->arg3);
			return Interpret_Triop(arg1, arg2, arg3);
		}
		virtual ValTy Interpret_Binop(const IRExpr* e) const {
			ValTy arg1 = InterpretExpr(e->Iex.Binop.arg1);
			ValTy arg2 = InterpretExpr(e->Iex.Binop.arg2);
			return Interpret_Binop(arg1, arg2);
		}
		virtual ValTy Interpret_Unop(const IRExpr* e) const {
			ValTy arg1 = InterpretExpr(e->Iex.Unop.arg);
			return Interpret_Unop(arg1);
		}
		virtual ValTy Interpret_Load(const IRExpr* e) const {
			ValTy addr = InterpretExpr(e->Iex.Load.addr);
			return memLoad(addr, e->Iex.Load.ty, e->Iex.Load.end);
		}
		virtual ValTy Interpret_Get(const IRExpr* e) const {
			return regGet(e->Iex.Get.offset, e->Iex.Get.ty);
		}
		virtual ValTy Interpret_GetI(const IRExpr* e) const {
			IRRegArray* descr = e->Iex.GetI.descr;
			ValTy ix = InterpretExpr(e->Iex.GetI.ix);
			return regGet(descr->base, e->Iex.GetI.bias, ix, descr->nElems, descr->elemTy);
		}
		ValTy InterpretExpr(const IRExpr* e) const {
			switch (e->tag)
			{
#define IEX(IexName) case Iex_##IexName: { return Interpret_##IexName(e); }
#include "instopt/tracer/IRSB.def"
#undef IEX
			default:
				VPANIC("InterpretExpr");
			}
		}



		virtual IRTypeEnv* getIRTypeEnv() = 0;
		virtual IRType typeOfIRExpr(const IRTypeEnv* tyenv, const IRExpr* e) { return ::typeOfIRExpr(tyenv, e); }

		virtual IstRetTy Interpret_Put(const IRStmt* st) {
			ValTy data = InterpretExpr(st->Ist.Put.data);
			return regPut(st->Ist.Put.offset, data);
		}
		virtual IstRetTy Interpret_PutI(const IRStmt* st) {
			IRPutI* puti;
			puti = st->Ist.PutI.details;
			IRRegArray* descr = puti->descr;
			ValTy ix = InterpretExpr(puti->ix);
			ValTy data = InterpretExpr(puti->data);
			return regPut(descr->base, puti->bias, ix, descr->nElems, descr->elemTy, data);
		}
		virtual IstRetTy Interpret_WrTmp(const IRStmt* st) {
			ValTy data = InterpretExpr(st->Ist.WrTmp.data);
			return Interpret_WrTmp(st->Ist.WrTmp.tmp, data);
		}
		virtual IstRetTy Interpret_Store(const IRStmt* st) {
			ValTy addr = InterpretExpr(st->Ist.Store.addr);
			ValTy data = InterpretExpr(st->Ist.Store.data);
			return Interpret_Store(addr, data, st->Ist.Store.end);
		}
		virtual IstRetTy Interpret_StoreG(const IRStmt* st) {
			IRStoreG* sg;
			sg = st->Ist.StoreG.details;
			ValTy addr = InterpretExpr(sg->addr);
			ValTy data = InterpretExpr(sg->data);
			ValTy guard = InterpretExpr(sg->guard);
			return Interpret_StoreG(guard, addr, data, sg->end);
		}
		virtual IstRetTy Interpret_LoadG(const IRStmt* st) const {
			IRLoadG* lg;
			lg = st->Ist.LoadG.details;
			ValTy addr = InterpretExpr(lg->addr);
			ValTy alt = InterpretExpr(lg->alt);
			ValTy guard = InterpretExpr(lg->guard);
			return Interpret_LoadG(lg->dst, guard, addr, alt, lg->cvt, lg->end);
		}
		virtual IstRetTy Interpret_CAS(const IRStmt* st) const {
			IRCAS* cas;
			cas = st->Ist.CAS.details;
			ValTy addr = InterpretExpr(cas->addr);
			ValTy expdLo = InterpretExpr(cas->expdLo);
			ValTy dataLo = InterpretExpr(cas->dataLo);
			llvm::Optional<ValTy> expdHi, dataHi;
			if (cas->expdHi)
				expdHi = InterpretExpr(cas->expdHi);
			if (cas->dataHi)
				dataHi = InterpretExpr(cas->dataHi);
			return Interpret_CAS(addr, expdLo, dataLo, expdHi, dataHi, cas->end);
		}
		virtual IstRetTy Interpret_LLSC(const IRStmt* st) {
			ValTy addr = InterpretExpr(st->Ist.LLSC.addr);
			ValTy storedata = InterpretExpr(st->Ist.LLSC.storedata);
			return Interpret_LLSC(st->Ist.LLSC.result, addr, storedata, st->Ist.LLSC.end);
		}
		//virtual void Interpret_Dirty(const IRStmt* st) {
		//    Int i;
		//    const IRDirty* d;
		//    d = st->Ist.Dirty.details;

		//    Int j;
		//    for (j = 0; j < d->nFxState; j++) {
		//        if (d->fxState[j].fx == Ifx_Modify || d->fxState[j].fx == Ifx_Write) {
		//            Int offset = d->fxState[i].offset;
		//            Int size = d->fxState[i].size;
		//            Int nRepeats = d->fxState[i].nRepeats;
		//            Int repeatLen = d->fxState[i].repeatLen;
		//            // regPut(offset, nRepeats * repeatLen + size);
		//        }
		//    }

		//    if (d->mFx != Ifx_None) {
		//        InterpretExpr(d->mAddr);
		//    }
		//    else {
		//        vassert(d->mAddr == NULL);
		//    }
		//    ValTy guard = InterpretExpr(d->guard);
		//    for (i = 0; d->args[i]; i++) {
		//        IRExpr* arg = d->args[i];
		//        if (LIKELY(!is_IRExpr_VECRET_or_GSPTR(arg)))
		//            InterpretExpr(arg);
		//    }
		//}
		virtual IstRetTy Interpret_NoOp(const IRStmt* st) {}
		virtual IstRetTy Interpret_MBE(const IRStmt* st) {
			return Interpret_MBE(st->Ist.MBE.event);
		}
		virtual IstRetTy Interpret_IMark(const IRStmt* st) {
			return Interpret_IMark(st->Ist.IMark.addr, st->Ist.IMark.len, st->Ist.IMark.delta);
		}
		virtual IstRetTy Interpret_AbiHint(const IRStmt* st) {
			ValTy base = InterpretExpr(st->Ist.AbiHint.base);
			ValTy nia = InterpretExpr(st->Ist.AbiHint.nia);
			return Interpret_AbiHint(base, nia);
		}
		virtual IstRetTy Interpret_Exit(const IRStmt* st) {
			ValTy guard = InterpretExpr(st->Ist.Exit.guard);
			Addr next;
			if (st->Ist.Exit.dst)
			{
				next = st->Ist.Exit.dst->Ico.U64;
				if (st->Ist.Exit.dst->tag == Ico_U32)
					next = (UInt)next;
			}
			return Interpret_Exit(guard, st->Ist.Exit.jk, next, st->Ist.Exit.offsIP);
		}

		virtual IstRetTy Interpret(const IRStmt* st) {
			switch (st->tag)
			{
#define IST(IstName) case Ist_##IstName: { return Interpret_##IstName(st); }
#include "instopt/tracer/IRSB.def"
#undef IST
			default:
				VPANIC("flatten_Stmt");
			};
		}
		virtual bool checkPreIRStmt(const IRStmt** stmt, Int i, Int stmts_used) {
			return true;
		}
		virtual bool checkPostIRStmt(const IRStmt** stmt, Int i, Int stmts_used, conIstRetTy stmtRet) {
			return true;
		}
		virtual void InterpretStmts(const IRStmt** stmts, Int stmts_used) {
			Int i;
			for (i = 0; i < stmts_used; i++)
			{
				const IRStmt* st = stmts[i];
				if (!checkPreIRStmt(stmts, i, stmts_used)) break;
				IstRetTy ret = Interpret(st);
				if (!checkPostIRStmt(stmts, i, stmts_used, ret)) break;
			}
		};
		virtual void InterpretNext(IRExpr* next, IRJumpKind jumpkind, Int offsIP) {};
		virtual void Interpret(const IRSB* irsb) {
			setTyEnv(irsb->tyenv);
			InterpretStmts(irsb->stmts, irsb->stmts_used);
			InterpretNext(irsb->next, irsb->jumpkind, irsb->offsIP);
		}
	};
}