
/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    Reister.class:
Abstract:
    API list;
Author:
    WXC 2019-05-31.
Revision History:
--*/

#include "engine/vex_context.h"
#include "engine/state_explorer.h"
#include "gen_global_var_call.hpp"
#include "engine/tr_kernel.h"

#ifdef _MSC_VER
#include <Windows.h>
#endif
using namespace TR;


z3::expr crypto_finder(StateBase& s, Addr64 base, Z3_ast index);

HMODULE hMod_crypto_analyzer = LoadLibraryA("libcrypto_analyzer.dll");

//TR::vex_context::Hook_idx2Value c_crypto_find32 = (TR::vex_context::Hook_idx2Value)GetProcAddress(hMod_crypto_analyzer, "?crypto_finder32@@YA?AVexpr@z3@@AEAV?$State@I@TR@@IPEAU_Z3_ast@@@Z");;
//TR::vex_context::Hook_idx2Value c_crypto_find64 = (TR::vex_context::Hook_idx2Value)GetProcAddress(hMod_crypto_analyzer, "?crypto_finder64@@YA?AVexpr@z3@@AEAV?$State@_K@TR@@_KPEAU_Z3_ast@@@Z");



int eval_all(std::deque<sv::tval>& result, z3::solver& solv, Z3_ast _exp) {
    //std::cout << nia << std::endl;
    //std::cout << state.solv.assertions() << std::endl;
    z3::context& ctx = solv.ctx();
    z3::expr exp(ctx, _exp);
    solv.push();

    auto sk = exp.get_sort().sort_kind();
    vassert(sk == Z3_BV_SORT);
    int nbits = exp.get_sort().bv_size();
    vassert(nbits <= 64);
    uint64_t realu64;
    for (int nway = 0; ; nway++) {
        auto ck = solv.check();
        if (ck == z3::unknown) return -1;
        if (ck == z3::sat) {
            z3::model m = solv.get_model();
            Z3_model_inc_ref(ctx, m);
            z3::expr re = m.eval(exp);
            //std::cout << re << std::endl;
            if (re.is_numeral_u64(realu64)) {
                result.emplace_back(sv::tval(ctx, realu64, nbits));
                solv.add(exp != re);
            }
            else {
                std::cout << re << std::endl;
                std::cout << solv.assertions() << std::endl;
                solv.pop();
                return -1;
            }
        }
        else {
#if defined(OPSTR)
            for (auto s : result) std::cout << ", " << s;
#endif
            solv.pop();
            //for (auto m : mv) Z3_model_dec_ref(ctx, m);
            return result.size();
        }
    }
};

//-1 err. 0 false. 1 true. 2 false || true.
int eval_all_bool(z3::solver& solv, Z3_ast _exp) {
    int ret = -1;
    Z3_decl_kind bool_L, bool_R;
    z3::context& ctx = solv.ctx();
    z3::expr exp(ctx, _exp);

   // std::cout << Z3_simplify_get_help(solv.ctx());
    //std::cout << exp.simplify() << std::endl;
    //std::cout << solv.assertions() << std::endl;

    solv.push();
    {
        auto sk = exp.get_sort().sort_kind();
        vassert(sk == Z3_BOOL_SORT);

        auto b1 = solv.check();
        if (b1 != z3::sat) {
            goto faild;
        }
        z3::model m1 = solv.get_model();
        z3::expr e1 = m1.eval(exp, true);
        bool_L = e1.decl().decl_kind();
        if (!(bool_L == Z3_OP_TRUE || bool_L == Z3_OP_FALSE))
            goto faild;


        //----------not-----------

        solv.add(exp != e1);
        auto b2 = solv.check();
        if (b2 == z3::unknown) {
            goto faild;
        }
        if (b2 == z3::unsat) {
            solv.pop();
            return bool_L == Z3_OP_TRUE;
        }

        solv.pop();
        return 2;
    }


faild: {
    std::cout << exp << std::endl;
    std::cout << solv.assertions() << std::endl;
    solv.pop();
    return -1;
    };

};







//
//z3::expr StateMEM::idx2Value(Addr64 base, Z3_ast idx)
//{
//
//    z3::expr result = m_vctx.idx2value(m_state, base, idx);
//    if ((Z3_ast)result) {
//        return result;
//    }
//    result = crypto_finder(m_state, base, idx);
//    return result;
//}



State::State(vex_context& vctx, VexArch guest_arch)
    : StateBase(vctx, guest_arch),
    m_irvex(nullptr),
    m_trace(std::make_shared<TraceInterface>(TR::CF_None))
{

    clean_dirty_mode();
};

State::State(State& father, HWord gse)
    : StateBase(father, gse),
    m_irvex(nullptr),
    m_trace(father.m_trace->mk_new_TraceInterface()),
    m_is_dirty_mode(father.m_is_dirty_mode)
{

}




State::~State() {
    if(m_dctx)
        dirty_context_del(m_dctx);
}

void TR::State::x86_set_mode(UChar cs)
{
    if (cs == 0x33 && vinfo().is_mode_32()) { // amd64
        vassert(vinfo().gguest() == VexArchX86);
        vinfo().enable_long_mode();
    }
    else if(cs == 0x23 && !vinfo().is_mode_32()){ // 32
        vassert(vinfo().gguest() == VexArchAMD64);
        vinfo().disable_long_mode();
    }
    else
    {
        logger->warn("cs : {:x} unkonow", cs);
    }
    regs.set(X86_IR_OFFSET::CS, (UShort)cs);
    if(m_irvex)
        irvex().set_vta_chunk(vinfo().gguest(), vinfo().gtraceflags());
    
};

template<>
InvocationStack<HWord>::operator std::string() const {
    std::string ret;
    char buff[100];
    UInt size = m_guest_saved_ret.size();
    auto gcs = m_guest_saved_ret.rbegin();
    for (UInt idx = 0; idx < size; idx++) {
        sprintf_s(buff, sizeof(buff), "0x%-16x :: 0x%-16x\n", gcs->first, gcs->second);
        ret.append(buff);
        gcs++;
    }
    return ret;

}


template<>
InvocationStack<tval>::operator std::string() const {
    std::string ret;
    char buff[100];
    UInt size = m_guest_saved_ret.size();
    auto gcs = m_guest_saved_ret.rbegin();
    for (UInt idx = 0; idx < size; idx++) {
        
        ret.append(gcs->first.str() + " :: ");
        ret.append(gcs->second.str() + "\n");
        gcs++;
    }
    return ret;

}




TR::TRsolver::TRsolver(z3::context& c)
    :
#if 0
    z3::solver(mk_tactic_solver_default(c))
#else
    z3::solver(c)
#endif
{
    m_asserts.reserve(2);
};

void TR::TRsolver::add(sbool const& e)
{
    if (!m_solver_snapshot) {
        m_solver_snapshot = true;
        push();
    }
    add_assert(e);
}

void TR::TRsolver::check_if_forget_pop()
{
    if (m_solver_snapshot) {
        m_solver_snapshot = false;
        pop();
    }
}

void TRsolver::add_assert(const sbool& t_assert)
{
    if ((Z3_context)t_assert != (Z3_context)(*this)) {
        add_assert(t_assert.translate(*this));
        return;
    }
    Z3_solver_assert(*this, *this, t_assert);
    if (!is_snapshot()) {
        m_asserts.push_back(t_assert);
    }
}

//DES等加密算法需要配置tactic策略才能求解出答案。
//z3::params m_params(m_ctx);
//z3::tactic m_tactic(with(tactic(m_ctx, "simplify"), m_params) &
//    tactic(m_ctx, "sat") &
//    tactic(m_ctx, "solve-eqs") &
//    tactic(m_ctx, "bit-blast") &
//    tactic(m_ctx, "smt")
//    &
//    tactic(m_ctx, "factor") &
//    tactic(m_ctx, "bv1-blast") &
//    tactic(m_ctx, "qe-sat") &
//    tactic(m_ctx, "ctx-solver-simplify") &
//    tactic(m_ctx, "nla2bv") &
//    tactic(m_ctx, "symmetry-reduce")/**/
//);
//state.setSolver(m_tactic);
z3::solver TR::TRsolver::mk_tactic_solver_default(z3::context& c)
{
    /*Legal parameters are :
      ctrl_c(bool) (default: true)
      dump_benchmarks(bool) (default: false)
      dump_models(bool) (default: false)
      elim_01(bool) (default: true)
      enable_sat(bool) (default: true)
      enable_sls(bool) (default: false)
      maxlex.enable(bool) (default: true)
      maxres.add_upper_bound_block(bool) (default: false)
      maxres.hill_climb(bool) (default: true)
      maxres.max_core_size(unsigned int) (default: 3)
      maxres.max_correction_set_size(unsigned int) (default: 3)
      maxres.max_num_cores(unsigned int) (default: 4294967295)
      maxres.maximize_assignment(bool) (default: false)
      maxres.pivot_on_correction_set(bool) (default: true)
      maxres.wmax(bool) (default: false)
      maxsat_engine(symbol) (default: maxres)
      optsmt_engine(symbol) (default: basic)
      pb.compile_equality(bool) (default: false)
      pp.neat(bool) (default: true)
      priority(symbol) (default: lex)
      rlimit(unsigned int) (default: 0)
      solution_prefix(symbol) (default:)
      timeout(unsigned int) (default: 4294967295)
    */
    z3::params t_params(c);
    //t_params.set("parallel.enable", true);
   
    z3::tactic t_tactic(
        z3::with(
            z3::tactic(c, "simplify"),
            t_params
        )
        & z3::tactic(c, "sat")
        & z3::tactic(c, "solve-eqs")
        & z3::tactic(c, "bit-blast")
        & z3::tactic(c, "smt")
        
        & z3::tactic(c, "factor")
        & z3::tactic(c, "bv1-blast")
         // &  z3::tactic(c, "qe-sat") 
        & z3::tactic(c, "ctx-solver-simplify")
        & z3::tactic(c, "nla2bv")
        & z3::tactic(c, "symmetry-reduce")
        
    );
    return t_tactic.mk_solver();
}

// -------------   dirty  -------------

DirtyCtx TR::State::getDirtyVexCtx()
{
    if(!m_dctx)
        m_dctx = dirty_context(this);
    return m_dctx;
};

sv::tval TR::State::dirty_call(const IRCallee* cee, IRExpr** exp_args, IRType ty)
{
    getDirtyVexCtx();
    dirty_ccall(m_dctx, cee, exp_args);
    return dirty_result(m_dctx, ty);
};

sv::tval TR::State::dirty_call(const HChar* name, void* func, std::initializer_list<rsval<Addr64>> parms, IRType ty)
{
    getDirtyVexCtx();
    dirty_call_np(m_dctx, name, func, parms);
    return dirty_result(m_dctx, ty);
};

HWord TR::State::getGSPTR()
{
    return dirty_get_gsptr(getDirtyVexCtx());
};

// -------------   dirty  -------------

template<typename T>
class DirtyFunction {
public:
    using Function_6 = ULong(*) (T, T, T, T, T, T);
    using Function_5 = ULong(*) (T, T, T, T, T);
    using Function_4 = ULong(*) (T, T, T, T);
    using Function_3 = ULong(*) (T, T, T);
    using Function_2 = ULong(*) (T, T);
    using Function_1 = ULong(*) (T);
    using Function_0 = ULong(*) ();

    using Z3_Function6 = rsval<T>(*) (sv::tval&, sv::tval&, sv::tval&, sv::tval&, sv::tval&, sv::tval&);
    using Z3_Function5 = rsval<T>(*) (sv::tval&, sv::tval&, sv::tval&, sv::tval&, sv::tval&);
    using Z3_Function4 = rsval<T>(*) (sv::tval&, sv::tval&, sv::tval&, sv::tval&);
    using Z3_Function3 = rsval<T>(*) (sv::tval&, sv::tval&, sv::tval&);
    using Z3_Function2 = rsval<T>(*) (sv::tval&, sv::tval&);
    using Z3_Function1 = rsval<T>(*) (sv::tval&);
};



#define CDFCHECK(arg0) if (arg0.symb()) { z3_mode = True; if (!cptr) { return dirty_call(cee, exp_args, ty); }; }


template<class T>
sv::tval dirty_result_check(const T& v, UShort nbits) {
    if (v.real()) {
        return sv::tval(v, (ULong)v.tor(), nbits);
    }
    else {
        return sv::tval(v, (Z3_ast)v.tos(), Z3_BV_SORT, nbits);
    }
}


// 不知道为什么DirtyFunction<ea_nbits>::Function_N 为什么不行，哎，编译器就tm离谱, 妥协一步
template<>
sv::tval TR::State::tIRCallee<32>(const IRCallee* cee, IRExpr** const exp_args, IRType ty)
{
    using DCF = DirtyFunction<UInt>;
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return sv::tval(ctx(), ((DCF::Function_0)(cee->addr))(), bitn);
    void* cptr = funcDict(cee->addr);
    if (cptr == DIRTY_CALL_MAGIC) {
        return dirty_call(cee, exp_args, ty);
    }
    sv::tval arg0 = tIRExpr(exp_args[0]); CDFCHECK(arg0);
    if (!exp_args[1]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function1)(cptr))(arg0), bitn) : sv::tval(m_ctx, ((DCF::Function_1)(cee->addr))(arg0), bitn);
    sv::tval arg1 = tIRExpr(exp_args[1]); CDFCHECK(arg1);
    if (!exp_args[2]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function2)(cptr))(arg0, arg1), bitn) : sv::tval(m_ctx, ((DCF::Function_2)(cee->addr))(arg0, arg1), bitn);
    sv::tval arg2 = tIRExpr(exp_args[2]); CDFCHECK(arg2);
    if (!exp_args[3]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function3)(cptr))(arg0, arg1, arg2), bitn) : sv::tval(m_ctx, ((DCF::Function_3)(cee->addr))(arg0, arg1, arg2), bitn);
    sv::tval arg3 = tIRExpr(exp_args[3]); CDFCHECK(arg3);
    if (!exp_args[4]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function4)(cptr))(arg0, arg1, arg2, arg3), bitn) : sv::tval(m_ctx, ((DCF::Function_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    sv::tval arg4 = tIRExpr(exp_args[4]); CDFCHECK(arg4);
    if (!exp_args[5]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4), bitn) : sv::tval(m_ctx, ((DCF::Function_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    sv::tval arg5 = tIRExpr(exp_args[5]); CDFCHECK(arg5);
    if (!exp_args[6]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn) : sv::tval(m_ctx, ((DCF::Function_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
    VPANIC("not support");
};
template<>
sv::tval TR::State::tIRCallee<64>(const IRCallee* cee, IRExpr** const exp_args, IRType ty)
{
    using DCF = DirtyFunction<ULong>;
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return sv::tval(ctx(), ((DCF::Function_0)(cee->addr))(), bitn);
    void* cptr = funcDict(cee->addr);
    if (cptr == DIRTY_CALL_MAGIC) {
        return dirty_call(cee, exp_args, ty);
    }
    sv::tval arg0 = tIRExpr(exp_args[0]); CDFCHECK(arg0);
    if (!exp_args[1]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function1)(cptr))(arg0), bitn) : sv::tval(m_ctx, ((DCF::Function_1)(cee->addr))(arg0), bitn);
    sv::tval arg1 = tIRExpr(exp_args[1]); CDFCHECK(arg1);
    if (!exp_args[2]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function2)(cptr))(arg0, arg1), bitn) : sv::tval(m_ctx, ((DCF::Function_2)(cee->addr))(arg0, arg1), bitn);
    sv::tval arg2 = tIRExpr(exp_args[2]); CDFCHECK(arg2);
    if (!exp_args[3]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function3)(cptr))(arg0, arg1, arg2), bitn) : sv::tval(m_ctx, ((DCF::Function_3)(cee->addr))(arg0, arg1, arg2), bitn);
    sv::tval arg3 = tIRExpr(exp_args[3]); CDFCHECK(arg3);
    if (!exp_args[4]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function4)(cptr))(arg0, arg1, arg2, arg3), bitn) : sv::tval(m_ctx, ((DCF::Function_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    sv::tval arg4 = tIRExpr(exp_args[4]); CDFCHECK(arg4);
    if (!exp_args[5]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4), bitn) : sv::tval(m_ctx, ((DCF::Function_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    sv::tval arg5 = tIRExpr(exp_args[5]); CDFCHECK(arg5);
    if (!exp_args[6]) return (z3_mode) ? dirty_result_check(((DCF::Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn) : sv::tval(m_ctx, ((DCF::Function_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
    VPANIC("not support");
};


#undef CDFCHECK


sv::tval TR::State::tCCall(const IRCallee* cee,  IRExpr** const exp_args, IRType ty)
{
    if (vinfo().is_mode_32()) {
        return tIRCallee<32>(cee, exp_args, ty);
    }
    else {
        return tIRCallee<64>(cee, exp_args, ty);
    }
}

inline sv::tval State::ILGop(const IRLoadG *lg) {
    switch (lg->cvt) {
    case ILGop_IdentV128:{ return vIex_Load(tIRExpr(lg->addr), Ity_V128);            }
    case ILGop_Ident64:  { return vIex_Load(tIRExpr(lg->addr), Ity_I64 );            }
    case ILGop_Ident32:  { return vIex_Load(tIRExpr(lg->addr), Ity_I32 );            }
    case ILGop_16Uto32:  { return vIex_Load(tIRExpr(lg->addr), Ity_I16 ).zext(16);   }
    case ILGop_16Sto32:  { return vIex_Load(tIRExpr(lg->addr), Ity_I16 ).sext(16);   }
    case ILGop_8Uto32:   { return vIex_Load(tIRExpr(lg->addr), Ity_I8  ).zext(8);    }
    case ILGop_8Sto32:   { return vIex_Load(tIRExpr(lg->addr), Ity_I8  ).sext(8);    }
    case ILGop_INVALID:
    default: VPANIC("ppIRLoadGOp");
    }
}

//void TR::State::do_Ijk_Ret(const tval& next)
//{
//    if UNLIKELY(m_is_dirty_mode) {
//        return;
//    }
//
//    /*   InvocationStack<tval> m_InvokStack;
//       if UNLIKELY(m_InvokStack.empty()) {
//           if (!m_call_stack_is_empty) {
//               m_call_stack_is_empty = true;
//               std::cout << "call stack end :: " << std::hex << get_cpu_ip() << std::endl;
//           }
//       }
//       else {
//           auto r = m_InvokStack.pop();
//       }*/
//
//    get_trace()->traceRet(*this, r.first, r.second);
//}
//
//void TR::State::do_Ijk_Call(const tval& next)
//{
//    using THWord = std::conditional_t<ea_nbits == 32, UInt, ULong>;
//    if UNLIKELY(m_is_dirty_mode) {
//        return;
//    }
//    auto bp = regs.get<THWord>(vinfo().gRegsBpOffset()).tor();
//
//    get_trace()->traceInvoke(*this, next, bp);
//    m_InvokStack.push(next, bp);
//    m_call_stack_is_empty = False;
//
//}




void TR::State::dirty_call_run(IRTemp tmp, IRType tmpType, const IRDirty* dirty)
{
    getDirtyVexCtx();
    dirty_run(m_dctx, dirty);
    if (dirty->tmp != IRTemp_INVALID) {
        irvex().operator[](dirty->tmp) = dirty_result(m_dctx, tmpType);
    }

}

sv::tval State::tIRExpr(const IRExpr* e)
{
    switch (e->tag) {
    case Iex_Get: { return vIex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
    case Iex_RdTmp: { return irvex().operator[](e->Iex.RdTmp.tmp); }
    case Iex_Unop: { return tUnop(e->Iex.Unop.op, tIRExpr(e->Iex.Unop.arg)); }
    case Iex_Binop: { return tBinop(e->Iex.Binop.op, tIRExpr(e->Iex.Binop.arg1), tIRExpr(e->Iex.Binop.arg2)); }
    case Iex_Triop: { return tTriop(e->Iex.Triop.details->op, tIRExpr(e->Iex.Triop.details->arg1), tIRExpr(e->Iex.Triop.details->arg2), tIRExpr(e->Iex.Triop.details->arg3)); }
    case Iex_Qop: { return tQop(e->Iex.Qop.details->op, tIRExpr(e->Iex.Qop.details->arg1), tIRExpr(e->Iex.Qop.details->arg2), tIRExpr(e->Iex.Qop.details->arg3), tIRExpr(e->Iex.Qop.details->arg4)); }
    case Iex_Load: { return vIex_Load(tIRExpr(e->Iex.Load.addr), e->Iex.Get.ty); }
    case Iex_Const: { return sv::tval(m_ctx, e->Iex.Const.con); }
    case Iex_ITE: {
        auto cond = tIRExpr(e->Iex.ITE.cond).tobool();
        if (cond.real()) {
            if (cond.tor()) {
                return tIRExpr(e->Iex.ITE.iftrue);
            }
            else {
                return tIRExpr(e->Iex.ITE.iffalse);
            }
        }
        else {
            return ite(cond.tos(), tIRExpr(e->Iex.ITE.iftrue), tIRExpr(e->Iex.ITE.iffalse));
        }
    }
    case Iex_CCall: { return tCCall(e->Iex.CCall.cee, e->Iex.CCall.args, e->Iex.CCall.retty); }
    case Iex_GetI: {
        auto ix = tIRExpr(e->Iex.GetI.ix);   /*  [e->Iex.GetI.ix, e->Iex.GetI.bias];  */
        if (ix.real()) {
            int re_ix = ix.tor<true, 32>();
            UInt regoff = e->Iex.GetI.descr->base + (((UInt)(e->Iex.GetI.bias + re_ix)) % e->Iex.GetI.descr->nElems) * ty2length(e->Iex.GetI.descr->elemTy);
            return vIex_Get(regoff, e->Iex.GetI.descr->elemTy);
        }
    };
    case Iex_GSPTR: { return sv::tval(m_ctx, getGSPTR(), sizeof(HWord) << 3); };
    case Iex_Binder: {
        Int binder = e->Iex.Binder.binder;
        spdlog::critical("tIRExpr Iex_Binder:  {}", binder);
    }
    case Iex_VECRET:{ }
    default:
        spdlog::critical("tIRExpr error:  {}", e->tag);
        VPANIC("not support");
    }
}


template<int ea_nbits>
void State::tIRStmt(const IRTypeEnv* tyenv, const IRStmt* s)
{

    switch (s->tag) {
    case Ist_WrTmp: { irvex()[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data); break; };
    case Ist_Put: { vIst_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
    case Ist_Store: { vIst_Store(tIRExpr(s->Ist.Store.addr).tors<false, ea_nbits>(), tIRExpr(s->Ist.Store.data)); break; };
    case Ist_PutI: {
        // PutI(840:8xI8)[t10,-1]
        // 840:arr->base
        // 8x :arr->nElems
        // I8 :arr->elemTy
        // t10:ix
        // -1 :e->Iex.GetI.bias
        auto ix = tIRExpr(s->Ist.PutI.details->ix);
        if (ix.real()) {
            int re_ix = ix.tor<true, 32>();
            UInt regoff = s->Ist.PutI.details->descr->base + (((UInt)((s->Ist.PutI.details->bias + re_ix))) % s->Ist.PutI.details->descr->nElems) * ty2length(s->Ist.PutI.details->descr->elemTy);
            vIst_Put(
                regoff,
                tIRExpr(s->Ist.PutI.details->data)
            );
        }
        else {
            vassert(0);
        }
        break;
    }
    case Ist_LoadG: { // load with guard
        IRLoadG* lg = s->Ist.LoadG.details;
        auto guard = tIRExpr(lg->guard).tobool();
        if LIKELY(guard.real()) {
            irvex()[lg->dst] = (guard.tor()) ? ILGop(lg) : tIRExpr(lg->alt);
        }
        else {
            irvex()[lg->dst] = ite(guard.tos(), ILGop(lg), tIRExpr(lg->alt));
        }
        break;
    }
    case Ist_StoreG: { // store with guard
        IRStoreG* sg = s->Ist.StoreG.details;
        auto addr = tIRExpr(sg->addr).tors<false, ea_nbits>();
        auto guard = tIRExpr(sg->guard).tobool();
        auto data = tIRExpr(sg->data);
        if LIKELY(guard.real()) {
            if (guard.tor()) {
                vIst_Store(addr, data);
            }
        }
        else {
            vIst_Store(addr, ite(guard.tos(), vIex_Load(addr,  data.nbits()), data));
        }
        break;
    }
    case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
        //  t15   = CASle(t31 ::t12   ->t13)
        //  oldLo = CASle(addr::expdLo->dataLo)
        //  解释
        //  oldLo = *addr  t15 = *t31
        //  *addr = dataLo *t31 = t13
        std::unique_lock<std::mutex> lock(m_state_lock);
        IRCAS cas = *(s->Ist.CAS.details);
        auto addr = tIRExpr(cas.addr).tors<false, ea_nbits>();//r10.value
        sv::tval expdLo = tIRExpr(cas.expdLo);
        sv::tval dataLo = tIRExpr(cas.dataLo);
        if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
            sv::tval expdHi = tIRExpr(cas.expdHi);
            sv::tval dataHi = tIRExpr(cas.dataHi);
            irvex()[cas.oldHi] = vIex_Load(addr, expdLo.nbits());
            irvex()[cas.oldLo] = vIex_Load(addr, expdLo.nbits());
            vIst_Store(addr, dataLo);
            vIst_Store(sv::tval(addr + (dataLo.nbits() >> 3)), dataHi);
        }
        else {//single
            irvex()[cas.oldLo] = vIex_Load(addr, expdLo.nbits());
            vIst_Store(addr, dataLo);
        }
        break;
    }
    case Ist_Dirty: {
        IRDirty* dirty = s->Ist.Dirty.details;
        rsbool guard = tIRExpr(dirty->guard).tobool();
        if UNLIKELY(guard.symb()) {
            VPANIC("auto guard = tIRExpr(dirty->guard); symbolic");
        }
        if LIKELY(guard.tor()) {
            IRType tmpTy = dirty->tmp == IRTemp_INVALID ? Ity_INVALID : typeOfIRTemp(tyenv, dirty->tmp);
            dirty_call_run(dirty->tmp, tmpTy, dirty);
        }
        break;// fresh changed block
    }
    case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/ {
        ppIRMBusEvent(s->Ist.MBE.event);
        break;
    }
    case Ist_LLSC:
    default: {
        spdlog::critical("what ppIRStmt {}", s->tag);
        VPANIC("what ppIRStmt");
    }
    };
}


template<int ea_nbits>
Vex_Kind State::emu_irsb_next(std::deque<BtsRefType>& tmp_branch, HWord& guest_start, irsb_chunk& bb) {
    using THWord = std::conditional_t<ea_nbits == 32, UInt, ULong>;
    const IRSB* irsb = bb->get_irsb();
    IRJumpKind jumpkind = irsb->jumpkind;
    tval _next = tIRExpr(irsb->next);
    sv::rsval<false, ea_nbits> next = _next.template tors<false, ea_nbits>();
    get_trace()->traceIRnext(*this, bb, _next);
    switch (jumpkind) {
    case Ijk_Ret: 
    case Ijk_Boring:
    case Ijk_Call: {
        break;
    }
    case Ijk_SigTRAP: {
        //software backpoint
        set_status(Exception);
    }
    default: {
        set_status(Ijk_call(jumpkind));
        if UNLIKELY(status() != Running) {
            return vStop;
        }
        if UNLIKELY(get_delta()) {
            guest_start = guest_start + get_delta();
            set_delta(0);
            return vUpdate;
        }
    }
    };

    //   Isb_next:

    
    if LIKELY(next.real()) {
        guest_start = next.tor();
    }
    else {
        std::deque<sv::tval> result;
        Int eval_size = eval_all(result, solv, next.tos());
        if (eval_size <= 0) {
            throw Expt::SolverNoSolution("eval_size <= 0", solv);
        }
        else if (eval_size == 1) {
            guest_start = result[0].tor<false, ea_nbits>();
        }
        else {
            for (auto re : result) {
                auto GN = re.tor<false, ea_nbits>();//guest next ip
                tmp_branch.push_back(std::make_shared<BtsType>(*this, (THWord)GN, next == (THWord)GN));
                tmp_branch.back()->set_jump_kd(jumpkind);
            }
            set_status(Fork);
            return vFork;
        }
    }
    
    return vUpdate;
}

bool false_exit_check(Addr& guard_false_entry, UInt IMark_stmtn, UInt exit_stmtn, const IRSB* irsb) {
    const IRStmt* exit_imark = irsb->stmts[IMark_stmtn];
    guard_false_entry = exit_imark->Ist.IMark.addr;
    if ((exit_stmtn + 1) < irsb->stmts_used) {
        UInt check_stmtn = IMark_stmtn + 1;
        for (const IRStmt* s = irsb->stmts[check_stmtn];
            check_stmtn < exit_stmtn;
            s = irsb->stmts[++check_stmtn])
        {
            IRStmtTag tag = s->tag;
            if (tag == Ist_NoOp || tag == Ist_WrTmp || tag == Ist_CAS) {
                continue;
            }
            else {
                ppIRStmt(s);
                VPANIC("dont support this error exit");
            };
        }
        const IRStmt* next_st = irsb->stmts[exit_stmtn + 1];
        if (next_st->tag == Ist_IMark) {
            // if (t4) { PUT(184) = 0x4120CE:I32; exit-Boring }
            // ---- IMark ----
            // ********
            // irsb next
            guard_false_entry = next_st->Ist.IMark.addr;
            return true;
        }
        /*
        if (t4) { PUT(184) = 0x4120CE:I32; exit-Boring }
        t5 = Sub32(t1,0x1:I32)
        PUT(24) = t5
        irsb next
        */
        return false;
    }
    else {
        /*
        if (t4) { PUT(184) = 0x4120CE:I32; exit-Boring }
        irsb next
        */
        if (irsb->next->tag == Iex_Const) {
            const IRConst* con = irsb->next->Iex.Const.con;
            guard_false_entry = con->Ico.U64;
            if (con->tag == Ico_U32) guard_false_entry &= 0xffffffff;
            return true;
        }
        return false;
    }

}

template<int ea_nbits>
TR::Vex_Kind State::emu_irsb(std::deque<BtsRefType>& tmp_branch, HWord& guest_start, State_Tag& status, irsb_chunk& bb) {

    using THWord = std::conditional_t<ea_nbits == 32, UInt, ULong>;
    IRSB* irsb = bb->get_irsb();
    const IRStmt* s = irsb->stmts[0];

    Hook_struct hs;
    UInt IMark_stmtn = 0;
    HWord block_start = guest_start;
    vassert(irsb->stmts[0]->tag == Ist_IMark);
    vassert(vinfo().gguest()==irvex().get_ir_vex_translate_args()->arch_guest);
    m_last_bb = bb;
    for (UInt stmtn = 0; stmtn < irsb->stmts_used; s = irsb->stmts[++stmtn])
    {
        get_trace()->traceIRStmtStart(*this, bb, stmtn);
        switch (s->tag)
        {
        case Ist_NoOp: break;
        case Ist_IMark: {
            guest_start = (THWord)s->Ist.IMark.addr;
            IMark_stmtn = stmtn;
            // 虚拟断点
            if (m_vctx.get_hook(hs, guest_start)) {
                get_trace()->setFlags(hs.cflag);
                if (!hs.cb) break;
                set_status(hs.cb(*this));
                if (this->status() != Running) {
                    return vStop;
                }
                if (get_delta()) {
                    guest_start = guest_start + get_delta();
                    set_delta(0);
                    return vUpdate;
                }
            }
            /*fresh changed block 检测执行base block时恶意修改该块指令*/
            if UNLIKELY(irvex().check()) { 
                return vUpdate; 
            }
            break;
        };
        case Ist_AbiHint: { //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
         /*   sv::tval nia = tIRExpr(s->Ist.AbiHint.nia);
            sv::tval bp = regs.get<THWord>(m_vinfo.gRegsBpOffset());
            get_trace()->traceInvoke(*this, nia, bp);*/
            break;
        }
        case Ist_Exit: {
            rsbool guard = tIRExpr(s->Ist.Exit.guard).tobool();
            if LIKELY(guard.real()) {
                if LIKELY(guard.tor()) {
                Exit_guard_true:
                    if (s->Ist.Exit.jk == Ijk_Boring)
                    {
                        guest_start = (THWord)s->Ist.Exit.dst->Ico.U64;
                        return vUpdate;
                    }
                    else {
                        if UNLIKELY((THWord)s->Ist.Exit.dst->Ico.U64 == guest_start) { // 异常循环
                            ppIRSB(irsb);
                        }
                        status = Ijk_call(s->Ist.Exit.jk);
                        if (status == Running) {
                            if (get_delta()) {
                                guest_start = guest_start + get_delta();
                                set_delta(0);
                                return vUpdate;
                            }
                            else { 
                                // pass this Ist_exit
                                break;
                            }
                        }
                        else {
                            return vStop;
                        }
                    }
                };
            }
            else {
                int ebool = eval_all_bool(solv, guard.tos());
                if (ebool < 0) {
                    throw Expt::SolverNoSolution("eval_size <= 0", solv);
                }
                if (ebool == 1) {
                    goto Exit_guard_true;
                }
                if (ebool == 2) {
                    status = Fork;
                    // guard true path
                    if (s->Ist.Exit.jk == Ijk_Boring) {
                        tmp_branch.push_back(std::make_shared<BtsType>(*this, (THWord)s->Ist.Exit.dst->Ico.U64, guard));
                    }
                    if (s->Ist.Exit.jk >= Ijk_SigILL && s->Ist.Exit.jk <= Ijk_SigFPE_IntOvf) {
                        tmp_branch.push_back(std::make_shared<BtsType>(*this, (THWord)s->Ist.Exit.dst->Ico.U64, guard));
                        tmp_branch.back()->set_jump_kd(s->Ist.Exit.jk);
                    }
                    // guard false path

                    Addr guard_false_entry;
                    if (false_exit_check(guard_false_entry, IMark_stmtn, stmtn, irsb)) {
                        tmp_branch.push_back(std::make_shared<BtsType>(*this, (THWord)guard_false_entry, !guard));
                    }
                    else {
                        vassert(guest_start == guard_false_entry);
                        tmp_branch.push_back(std::make_shared<BtsType>(*this, (THWord)guest_start, !guard));
                    }
                    return vFork;
                }
            }
            break;
        }
        default:
            tIRStmt<ea_nbits>(irsb->tyenv, s);
        }

        get_trace()->traceIRStmtEnd(*this, bb, stmtn);
    }

    return emu_irsb_next<ea_nbits>(tmp_branch, guest_start, bb);

//fork_exit:
//    {
//        sv::rsval<false, ea_nbits> next = tIRExpr(irsb->next).template tors<false, ea_nbits>();
//        if LIKELY(next.real()) {
//            tmp_branch.push_back(std::make_shared<BtsType>(*this, (THWord)next.tor(), !fork_exit_guard));
//        }
//        else {
//            std::deque<sv::tval> result;
//            Int eval_size = eval_all(result, solv, next.tos());
//            if (eval_size <= 0) {
//                throw Expt::SolverNoSolution("eval_size <= 0", solv);
//            }
//            else if (eval_size == 1) {
//                auto GN = result[0].tor<false, ea_nbits>();
//                tmp_branch.push_back(std::make_shared<BtsType>(*this, (HWord)GN, !fork_exit_guard));
//            }
//            else {
//                for (auto re : result) {
//                    auto GN = re.tor<false, ea_nbits>();//guest next ip
//                    tmp_branch.push_back(std::make_shared<BtsType>(*this, (THWord)GN, !fork_exit_guard, next == (THWord)GN));
//                }
//            }
//        }
//        return vFork;
//    }
}


bool State::vex_main_loop(std::deque<BtsRefType>& tmp_branch, irsb_chunk& irsb_chunk, HWord& guest_start, Addr avoid) {

    

    if UNLIKELY(jump_kd() != Ijk_Boring) {
        set_status(Ijk_call(jump_kd()));
        set_jump_kd(Ijk_Boring);
        if (status() != Running) {
            return false;
        }
    }

    if UNLIKELY(get_delta()) {
        guest_start = guest_start + get_delta();
        set_delta(0);
    }

    Vex_Kind vkd;

    do {
        irsb_chunk = irvex().translate_front(guest_start);
        IRSB* irsb = irsb_chunk->get_irsb();
        //ppIRSB(irsb);
        get_trace()->traceIRSB(*this, guest_start, irsb_chunk);
        if (vinfo().is_mode_32()) {
            vkd = emu_irsb<32>(tmp_branch, guest_start, m_status, irsb_chunk);
        }
        else {
            vkd = emu_irsb<64>(tmp_branch, guest_start, m_status, irsb_chunk);
        }
        get_trace()->traceIrsbEnd(*this, irsb_chunk);
        if (guest_start == avoid) {
            break;
        }

    }while (vkd == TR::Vex_Kind::vUpdate);

    
    //mem.set(nullptr);
    return true;
}

std::deque<TR::State::BtsRefType> TR::State::start(HWord ep)
{
    guest_start = ep;
    guest_start_ep = ep; 
    return start();
}


std::deque<TR::State::BtsRefType> TR::State::start() {
    if (vinfo().gguest() == VexArchAMD64 || vinfo().gguest() == VexArchX86) {
        x86_set_mode(regs.get<Ity_I16>(X86_IR_OFFSET::CS).tor());
    }
    
    clean_dirty_mode();
    set_mem_access(std::make_shared<TR::State::StateData<32>>(mem, regs));
    return start(guest_start, std::make_shared< EmuEnvGuest>(vctx(), vinfo(), mem), 0);
}

std::deque<TR::State::BtsRefType> TR::State::start(HWord& guest_start, std::shared_ptr<EmuEnvironment> e, Addr avoid) {
    mem.set_emu_env(e);
    m_irvex = e;
    return v_start(guest_start, avoid);
}

static void logger_function(const HChar* bytes, SizeT nbytes) {

}


std::deque<TR::State::BtsRefType> TR::State::v_start(HWord& guest_start, Addr avoid) {
    set_status(Running);
    get_trace()->traceStart(*this, guest_start);
    irsb_chunk irsb;
    std::deque<BtsRefType> tmp_branch;
Begin_try:
    try {
        irvex().malloc_ir_buff(m_ctx);
        vex_main_loop(tmp_branch, irsb, guest_start, avoid);
        irvex().free_ir_buff();
    }
    catch (Expt::ExceptionBase& error) {
        //mem.set(nullptr);
        if (1) {

            for (Int i = 0; i < irsb->get_irsb()->tyenv->types_used; i++) {
                logger->warn(" >> t{0:d} {1:s}", i, irvex()[i].str());
            }
            ppIR pp(logger);
            pp.ppIRSB(irsb->get_irsb());

            auto b1 = solv.check();
            if (b1 == z3::sat) {
                z3::model m1 = solv.get_model();
                std::string ms = m1.to_string();
                logger->warn(" payload : {:s} ", ms);
            }
            
        }
        logger->flush();
        logger->dump_backtrace();
        spdlog::disable_backtrace();
        spdlog::warn(" >> see exception contenxt {} at {}", error.msg(), get_log_path());
        irvex().free_ir_buff();
        switch (error.errTag()) {
        case Expt::GuestRuntime_exception:
        case Expt::GuestMem_read_err:
        case Expt::GuestMem_write_err: {
            try {
                cpu_exception(error);
            }
            catch (Expt::ExceptionBase& cpu_exception_error) {
                spdlog::warn("Usage issues or simulation software problems.\nError message:");
                spdlog::warn(error.msg());
                logger->warn("Usage issues or simulation software problems.\nError message:");
                logger->warn(error.msg());
                set_status(Death);
            }
            break;
        }
        case Expt::IR_failure_exit: {
            spdlog::critical("Sorry This could be my design error. (BUG)\nError message:");
            spdlog::critical(error.msg());
            {
                ppIR pp(spdlog::default_logger(), spdlog::level::critical);
                pp.ppIRSB(irsb->get_irsb());
            }
            exit(1);
        }
        case Expt::Solver_no_solution: {
            spdlog::critical(" There is no solution to this problem. But this COULD BE my design error (BUG).\nError message:");
            spdlog::critical(error.msg());
            exit(1);
        }
        };
    }

    if (status() == Exception) {
        set_status(Running);
        goto Begin_try;
    }

    get_trace()->traceFinish(*this, guest_start);

    return tmp_branch;
}


void State::branchGo()
{
    for(auto b : branch){
       m_vctx.pool().enqueue([b] {
          
            });
    }
}


void TR::State::set_irvex(std::shared_ptr<EmuEnvironment> e)
{
    m_irvex = e;
    if (e) {
        e->set_guest_bb_insn_control_obj();
    }
}

#include "engine/compress.h"

class StateCmprsInterface {
    cmpr::StateType m_type;
    cmpr::CmprsContext<State, State_Tag>& m_ctx;
    State& m_state;
    sbool m_condition;
    static bool StateCompression(State& a, State const& next) {
        //bool ret = a.m_InvokStack == next.m_InvokStack;// 压缩条件
        return a.StateCompression(next);//支持扩展条件
    }

    static void StateCompressMkSymbol(State& a, State const& newState) {
        //a.m_InvokStack = newState.m_InvokStack;// 使其满足压缩条件
        a.StateCompressMkSymbol(newState);//支持
    }

    std::vector<sbool> const & get_asserts() const { return m_state.solv.get_asserts(); };

public:
    StateCmprsInterface(
        cmpr::CmprsContext<State, State_Tag>& ctx,
        State& self,
        cmpr::StateType type
    ) :
        m_ctx(ctx), m_state(self), m_type(type), m_condition(m_ctx.ctx())
    { };

    cmpr::CmprsContext<State, State_Tag>& cctx() { return m_ctx; }
    cmpr::StateType type() { return m_type; };

    sbool const& get_assert() { 
        if (!(Z3_ast)m_condition) {
            m_condition = logic_and(get_asserts()).translate(m_ctx.ctx());
        }
        return m_condition;
    }

    void get_write_map(HASH_MAP<Addr64, bool>& record) {
        /*if (m_state.regs.getRecord()) {
            for (auto offset : *m_state.regs.getRecord()) {
                record[offset];
            }
        }*/
        /*
        for (auto mcm : m_state.mem.change_map()) {
            vassert(mcm.second->getRecord() != NULL);
            for (auto offset : *(mcm.second->getRecord())) {
                auto Address = mcm.first + offset;
                auto p = m_state.mem.get_mem_page(Address);
                vassert(p);
                vassert(p->get_user() == mem.get_user());
                vassert(Address > REGISTER_LEN);
                record[Address];
            }
        }*/
    }

    auto& branch() { return m_state.branch; };

    cmpr::StateType tag(State* son) {
        if (son->status() == Fork) {
            return cmpr::Fork_Node;
        };
        if (m_ctx.is_avoid(son->status())) {
            return cmpr::Avoid_Node;
        };
        if (son->get_cpu_ip() == m_ctx.get_target_addr()) {
            return static_cast<cmpr::StateType>(get_group_id(son));
        }
        return cmpr::Survive_Node;
    };

    Int get_group_id(State* s) {
        UInt group_count = 0;
        for (auto gs : m_ctx.group()) {
            if (StateCompression(*gs, *s)) {
                return group_count;
            }
            group_count++;
        }
        m_ctx.group().emplace_back(s);
        return group_count;
    }

    void del_obj() {
        delete& m_state;
    }

    PACK mem_Load(HWord addr) {
        return m_state.mem.template load<Ity_I64>(addr).translate(m_ctx.ctx());
    }

    PACK reg_Get(UInt offset) {
        return m_state.regs.template get<Ity_I64>(offset).translate(m_ctx.ctx());
    }

    PACK read(HWord addr) {
        if (addr < REGISTER_LEN) {
            return reg_Get(addr);
        }
        else {
            return mem_Load(addr);
        }
    }

    StateCmprsInterface* mk(State* son, cmpr::StateType tag) {
        //实际上少于4个case intel编译器会转为if
        switch (tag) {
        case cmpr::Fork_Node:return new cmpr::CmprsFork<StateCmprsInterface>(m_ctx, *son);
        case cmpr::Avoid_Node:return new cmpr::CmprsAvoid<StateCmprsInterface>(m_ctx, *son);
        case cmpr::Survive_Node:return new cmpr::CmprsSurvive<StateCmprsInterface>(m_ctx, *son);
        default:return new cmpr::CmprsTarget<StateCmprsInterface>(m_ctx, *son, tag);
        };

    }

    virtual bool has_survive() { return false; }
    virtual cmpr::CmprsFork<StateCmprsInterface>& get_fork_node() { VPANIC("???"); }
    virtual cmpr::CmprsTarget<StateCmprsInterface>& get_target_node() { VPANIC("???"); }
    virtual ~StateCmprsInterface() {};
};
#ifdef _DEBUG
#define PPCMPR
#endif


void TR::State::compress(cmpr::CmprsContext<State, State_Tag>& ctx)
{
    cmpr::Compress<StateCmprsInterface, State, State_Tag> cmp(ctx, *this);
    if (!ctx.group().size()) { 
        return;
    }
    else if (ctx.group().size() > 1 || (ctx.group().size() == 1 && cmp.has_survive())) {

        for (cmpr::Compress<StateCmprsInterface, State, State_Tag>::Iterator::StateRes state : cmp) {
            State* nbranch = (State*)ForkState(ctx.get_target_addr());
            sv::tval condition = state.conditions().translate(*nbranch);
#ifdef  PPCMPR
            printf("%s\n", Z3_ast_to_string(condition, condition));
#endif //  _DEBUG
            nbranch->solv.add_assert(condition);
            HASH_MAP<Addr64, cmpr::GPMana> const& cm = state.changes();
            HASH_MAP<Addr64, cmpr::GPMana>::const_iterator itor = cm.begin();
            HASH_MAP<Addr64, cmpr::GPMana>::const_iterator end = cm.end();

            for (; itor != end; itor++) {
                Addr64 addr = itor->first;
                sv::tval value = itor->second.get().translate(*nbranch);
#ifdef  PPCMPR
                printf("%p : {  %s  }\n", itor->first, Z3_ast_to_string(value, value));
#endif //  _DEBUG
                if (addr > REGISTER_LEN) {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    nbranch->vIst_Store(tval(m_ctx, addr), value);
                }
                else {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    nbranch->regs.Ist_Put(addr, value);
                }
            }
        }
    }
    else {
        for (cmpr::Compress<StateCmprsInterface, State, State_Tag>::Iterator::StateRes state : cmp) {
            sv::tval condition = state.conditions();
#ifdef  PPCMPR
            printf("%s\n", Z3_ast_to_string(condition, condition));
#endif //  _DEBUG
            solv.add_assert(condition);
            HASH_MAP<Addr64, cmpr::GPMana> const& cm = state.changes();
            HASH_MAP<Addr64, cmpr::GPMana>::const_iterator itor = cm.begin();
            HASH_MAP<Addr64, cmpr::GPMana>::const_iterator end = cm.end();
            cmp.clear_nodes();
            for (; itor != end; itor++) {
                Addr64 addr = itor->first;
                sv::tval value = itor->second.get();
#ifdef  PPCMPR
                printf("%p : {  %s  }\n", itor->first, Z3_ast_to_string(value, value));
#endif //  _DEBUG
                if (addr > REGISTER_LEN) {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    vIst_Store(tval(m_ctx, addr), value);
                }
                else {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    regs.Ist_Put(addr, value);
                }
            }
        }
        guest_start = ctx.get_target_addr();
        set_status(NewState);
    }
}




const char* constStrIRJumpKind(IRJumpKind kind)
{
    switch (kind) {
    case Ijk_Boring:        return ("Boring"); break;
    case Ijk_Call:          return ("Call"); break;
    case Ijk_Ret:           return ("Return"); break;
    case Ijk_ClientReq:     return ("ClientReq"); break;
    case Ijk_Yield:         return ("Yield"); break;
    case Ijk_EmWarn:        return ("EmWarn"); break;
    case Ijk_EmFail:        return ("EmFail"); break;
    case Ijk_NoDecode:      return ("NoDecode"); break;
    case Ijk_MapFail:       return ("MapFail"); break;
    case Ijk_InvalICache:   return ("InvalICache"); break;
    case Ijk_FlushDCache:   return ("FlushDCache"); break;
    case Ijk_NoRedir:       return ("NoRedir"); break;
    case Ijk_SigILL:        return ("SigILL"); break;
    case Ijk_SigTRAP:       return ("SigTRAP"); break;
    case Ijk_SigSEGV:       return ("SigSEGV"); break;
    case Ijk_SigBUS:        return ("SigBUS"); break;
    case Ijk_SigFPE:        return ("SigFPE"); break;
    case Ijk_SigFPE_IntDiv: return ("SigFPE_IntDiv"); break;
    case Ijk_SigFPE_IntOvf: return ("SigFPE_IntOvf"); break;
    case Ijk_Sys_syscall:   return ("Sys_syscall"); break;
    case Ijk_Sys_int32:     return ("Sys_int32"); break;
    case Ijk_Sys_int128:    return ("Sys_int128"); break;
    case Ijk_Sys_int129:    return ("Sys_int129"); break;
    case Ijk_Sys_int130:    return ("Sys_int130"); break;
    case Ijk_Sys_int145:    return ("Sys_int145"); break;
    case Ijk_Sys_int210:    return ("Sys_int210"); break;
    case Ijk_Sys_sysenter:  return ("Sys_sysenter"); break;
    default:                return ("ppIRJumpKind");
    }
}


unsigned int IRConstTag2nb(IRConstTag t) {
    switch (t) {
    case Ico_U1:
    case Ico_U8:	return 1;
    case Ico_U16:	return 2;
    case Ico_U32:	return 4;
    case Ico_U64:	return 8;
    case Ico_F32:	return 4;
    case Ico_F32i:	return 4;
    case Ico_F64:	return 8;
    case Ico_F64i:	return 8;
    case Ico_V128:	return 16;
    case Ico_V256:	return 32;
    }
    return 0;
}


unsigned int ty2length(IRType ty) {
    switch (ty) {
    case Ity_INVALID: VPANIC("Ity_INVALID"); break;
    case 1:
    case Ity_I1:      return 0;
    case 8:
    case Ity_I8:      return 1;
    case 16:
    case Ity_I16:     return 2;
    case Ity_F16:     return 2;
    case 32:
    case Ity_I32:     return 4;
    case Ity_D32:     return 4;
    case Ity_F32:     return 4;
    case 64:
    case Ity_I64:     return 8;
    case Ity_F64:     return 8;
    case Ity_D64:     return 8;
    case 128:
    case Ity_I128:    return 16;
    case Ity_F128:    return 16;
    case Ity_D128:    return 16;
    case Ity_V128:    return 16;
    case 256:
    case Ity_V256:    return 32;
    default:VPANIC("ty2length");
    }
    return 0;
}

unsigned int ty2bit(IRType ty) {
    switch (ty) {
    case Ity_INVALID: VPANIC("Ity_INVALID"); break;
    case 1:
    case Ity_I1:      return 1;
    case 8:
    case Ity_I8:      return 8;
    case 16:
    case Ity_I16:     return 16;
    case Ity_F16:     return 16;
    case 32:
    case Ity_I32:     return 32;
    case Ity_F32:     return 32;
    case Ity_D32:     return 32;
    case 64:
    case Ity_I64:     return 64;
    case Ity_F64:     return 64;
    case Ity_D64:     return 64;
    case 128:
    case Ity_I128:    return 128;
    case Ity_F128:    return 128;
    case Ity_D128:    return 128;
    case Ity_V128:    return 128;
    case 256:
    case Ity_V256:    return 256;
    default:VPANIC("ty2length");
    }
    return 0;
}


IRType length2ty(UShort bit) {
    switch (bit) {
    case 0:    return Ity_INVALID;
    case 1:    return Ity_I1;
    case 8:    return Ity_I8;
    case 16:   return Ity_I16;
    case 32:   return Ity_I32;
    case 64:   return Ity_I64;
    case 128:  return Ity_I128;
    case 256:  return Ity_V256;
    default:VPANIC("length2ty");
    }
    return Ity_INVALID;
}


//
//
//unsigned int TRCurrentThreadId() {
//    //teb+0x48
//    uint32_t* teb = (uint32_t*)__readgsqword(0x30);
//    return teb[0x12];
//}


z3::expr crypto_finder(StateBase& s, Addr64 base, Z3_ast index) {
   /* if (c_crypto_find32) {
        return c_crypto_find32(s, base, index);
    }*/
    VPANIC("gg");
    return z3::expr(s);
}


unsigned currentThreadId() {
    unsigned ThreadID;
#if defined(__APPLE__)
    asm("mov %%gs:0x00,%0" : "=r"(ThreadID));
#elif defined(__i386__)
    asm("mov %%gs:0x08,%0" : "=r"(ThreadID));
#elif defined(__x86_64__)
    asm("mov %%gs:0x10,%0" : "=r" (ThreadID));
#else
#error Unsupported architecture
#endif
    return ThreadID;
}


template<typename THword>
void State::vex_push(const rsval<THword>& v)
{
    if (vinfo().is_mode_32()) {
        rsval<UInt> sp = regs.get<ULong>(m_vinfo.gRegsSpOffset()) - sizeof(UInt);
        regs.set(m_vinfo.gRegsSpOffset(), sp);
        mem.store(sp, v);
    }
    else {
        rsval<ULong> sp = regs.get<ULong>(m_vinfo.gRegsSpOffset()) - sizeof(ULong);
        regs.set(m_vinfo.gRegsSpOffset(), sp);
        mem.store(sp, v);
    }
}

template<typename THword>
rsval<THword> State::vex_pop()
{
    if (vinfo().is_mode_32()) {
        rsval<UInt> sp = regs.get<UInt>(m_vinfo.gRegsSpOffset());
        regs.set(m_vinfo.gRegsSpOffset(), sp + sizeof(UInt));
        return mem.load<THword>(sp);
    }
    else {
        rsval<ULong> sp = regs.get<ULong>(m_vinfo.gRegsSpOffset());
        regs.set(m_vinfo.gRegsSpOffset(), sp + sizeof(ULong));
        return mem.load<THword>(sp);
    }
    
}

template<typename THword>
rsval<THword> State::vex_stack_get(int n)
{
    if (vinfo().is_mode_32()) {
        rsval<UInt> sp = regs.get<UInt>(m_vinfo.gRegsSpOffset());
        return mem.load<THword>(sp + (UInt)(n * sizeof(UInt)));
    }
    else {
        rsval<ULong> sp = regs.get<ULong>(m_vinfo.gRegsSpOffset());
        return mem.load<THword>(sp + (ULong)(n * sizeof(ULong)));
    }
}


template void State::vex_push<ULong>(const rsval<ULong>& v);
template void State::vex_push<UInt>(const rsval<UInt>& v);
template void State::vex_push<Long>(const rsval<Long>& v);
template void State::vex_push<Int >(const rsval<Int>& v);

template rsval<ULong> State::vex_pop<ULong>();
template rsval<UInt> State::vex_pop<UInt>();
template rsval<Long> State::vex_pop<Long>();
template rsval<Int > State::vex_pop<Int >();


template rsval<ULong> State::vex_stack_get<ULong>(int);
template rsval<UInt> State::vex_stack_get<UInt>(int);
template rsval<Long> State::vex_stack_get<Long>(int);
template rsval<Int > State::vex_stack_get<Int >(int);

#undef CODEDEF1
#undef CODEDEF2





State_Tag TR::State::Ijk_call(IRJumpKind jk)
{
    if (vctx().param().is_exist("Kernel")) {
        Ke::Kernel* kernel = (Ke::Kernel*)vctx().param().get("Kernel")->value();
        return kernel->Ijk_call(*this, jk);
    }
    return Death;
}

void TR::State::cpu_exception(Expt::ExceptionBase const& e)
{
    if (vctx().param().is_exist("Kernel")) {
        Ke::Kernel* kernel = (Ke::Kernel*)vctx().param().get("Kernel")->value();
        kernel->cpu_exception(*this, e);
    }
}

void TR::State::avoid_anti_debugging() {
    if (vctx().param().is_exist("Kernel")) {
        Ke::Kernel* kernel = (Ke::Kernel*)vctx().param().get("Kernel")->value();
        kernel->avoid_anti_debugging(*this);
    }
}

void TR::State::clean()
{
    dirty_context_del(m_dctx);
    m_dctx = nullptr;
}

void TraceInterface::pp_call_space(State& s)
{
    //UInt size = s.get_InvokStack().size();
    UInt size = 0;
    /*if (s.is_dirty_mode()) {
        s.logger->debug("D[{:2d}:{:2d}]", size, s.mem.get_user());
    }
    else {
        s.logger->debug("[{:2d}:{:2d}]", size, s.mem.get_user());
    }*/
    /*for (UInt i = 0; i < size; i++) {
        s.logger->debug("  ");
    }*/
}


void   TraceInterface::traceStart(State& s, HWord ea) {
    if (!s.logger->should_log(s.logger->level())) return;
    if (getFlag(TR::CF_traceState)) {
        s.logger->info("+++++++++++++++ Thread ID: {} ea: 0x{:x}  Started +++++++++++++++", currentThreadId(), ea);
    };
    s.logger->info("oep: 0x{:x} ", ea);
}

void   TraceInterface::traceFinish(State& s, HWord ea) {
    if (!s.logger->should_log(s.logger->level())) return;
    if (getFlag(TR::CF_traceState)) {
        ppIR pp(s.logger);
        if (s.status() == TR::Fork) {
            pp.vex_printf("\nFork from : %p to : { \n ", ea);
            for (auto bc : s.branch) {
                pp.vex_printf(" %p", bc->get_state_ep());
            }
            pp.vex_printf("\n };", ea);
            
        }
        s.logger->info("+++++++++++++++ Thread ID: {} ea: 0x{:x}  OVER +++++++++++++++", currentThreadId(), ea);
    }
};

void TraceInterface::traceIRStmtStart(State& s, irsb_chunk& irsb, UInt stmtn)
{

    if (!s.logger->should_log(s.logger->level())) return;

   /* if (getFlag(TR::CF_ppStmts)) {
        pp_call_space(s);
        IRStmt* st = irsb->get stmts[stmtn];
    }*/
};
void   TraceInterface::traceIRStmtEnd(State& s, irsb_chunk& irsb, UInt stmtn) {

    if (!s.logger->should_log(s.logger->level())) return;

    if (getFlag(TR::CF_ppStmts)) {
        ppIR pp(s.logger);

        IRStmt* st = irsb->get_irsb()->stmts[stmtn];
        //if (st->tag == Ist_WrTmp) {
        //    UInt tmp = st->Ist.WrTmp.tmp;
        //    vex_printf("\t=\t{:s}", s.irvex()[tmp].str());
        //}
        //else {
        //    //vex_printf("\n")
        //}

        if (st->tag == Ist_WrTmp) {
            UInt tmp = st->Ist.WrTmp.tmp;
            pp.vex_printf("t%u = ", tmp, s.irvex()[tmp].str().c_str());
            pp.ppIRExpr(st->Ist.WrTmp.data);
            pp.vex_printf("\t%s", s.irvex()[tmp].str().c_str());
        }
        else {
            pp.ppIRStmt(st);
        }
    }
}
void TR::TraceInterface::traceIRnext(State& s, irsb_chunk& irsb, const tval& val)
{

}
//void TR::TraceInterface::traceInvoke(State& s, const tval& call, const tval& bp)
//{
//    if (getFlag(TR::CF_traceInvoke)) {
//        pp_call_space(s, s.get_cpu_ip());
//        std::cout << "Invoke: " << call.str() << " bp: " << bp.str() << std::endl;
//    }
//}
//void TR::TraceInterface::traceRet(State& s, const tval& next)
//{
//
//    if (getFlag(TR::CF_traceInvoke)) {
//        pp_call_space(s, s.get_cpu_ip());
//        std::cout << "Ret   : " << next.str() << std::endl;
//    }
//}
//;

void   TraceInterface::traceIRSB(State& s, HWord ea, irsb_chunk& bb) {
    if (getFlag(TR::CF_traceJmp)) {
        pp_call_space(s);
        s.logger->debug("Jmp: %llx", ea);
        //ppIRSB(bb);
    }
}
void  TraceInterface::traceIrsbEnd(State& s, irsb_chunk&)
{
    return;
}
