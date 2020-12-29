
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
#include "state_class.h"
#include "gen_global_var_call.hpp"

#ifdef _MSC_VER
#include <Windows.h>
#endif
using namespace TR;

template<typename THword>
z3::expr crypto_finder(TR::State<THword>& s, Addr64 base, Z3_ast index);

HMODULE hMod_crypto_analyzer = LoadLibraryA("libcrypto_analyzer.dll");

TR::vex_context<Addr32>::Hook_idx2Value c_crypto_find32 = (TR::vex_context<Addr32>::Hook_idx2Value)GetProcAddress(hMod_crypto_analyzer, "?crypto_finder32@@YA?AVexpr@z3@@AEAV?$State@I@TR@@IPEAU_Z3_ast@@@Z");;
TR::vex_context<Addr64>::Hook_idx2Value c_crypto_find64 = (TR::vex_context<Addr64>::Hook_idx2Value)GetProcAddress(hMod_crypto_analyzer, "?crypto_finder64@@YA?AVexpr@z3@@AEAV?$State@_K@TR@@_KPEAU_Z3_ast@@@Z");

static Bool TR_initdone;
clock_t tr_begin_run = clock();


//######################StateMEM START##############################

template class TR::StateMEM<Addr32>;
template class TR::StateMEM<Addr64>;

//######################StateMEM END##############################



__attribute__((noreturn))
static void failure_exit() {
    throw Expt::IRfailureExit("valgrind error exit");
}

static void _vex_log_bytes(const HChar* bytes, SizeT nbytes) {
    std::cout << bytes;
}


UInt arch_2_stack_sp_iroffset(VexArch arch) {
    switch (arch) {
    case VexArchX86:return offsetof(VexGuestX86State, guest_ESP);
    case VexArchAMD64:return offsetof(VexGuestAMD64State, guest_RSP);
    case VexArchARM:return offsetof(VexGuestARMState, guest_R13);
    case VexArchARM64:return offsetof(VexGuestARM64State, guest_XSP);
    case VexArchPPC32:return offsetof(VexGuestPPC32State, guest_GPR1);
    case VexArchPPC64:return offsetof(VexGuestPPC64State, guest_GPR1);
    case VexArchS390X:return offsetof(VexGuestS390XState, guest_r15);
    case VexArchMIPS32:return offsetof(VexGuestMIPS32State, guest_r29);
    case VexArchMIPS64:return offsetof(VexGuestPPC64State, guest_GPR1);
    default:
        VPANIC("Invalid arch in setSP.\n");
        break;
    }
}



std::string replace(const char* pszSrc, const char* pszOld, const char* pszNew)
{
    std::string strContent, strTemp;
    strContent.assign(pszSrc);
    std::string::size_type nPos = 0;
    while (true)
    {
        nPos = strContent.find(pszOld, nPos);
        strTemp = strContent.substr(nPos + strlen(pszOld), strContent.length());
        if (nPos == std::string::npos)
        {
            break;
        }
        strContent.replace(nPos, strContent.length(), pszNew);
        strContent.append(strTemp);
        nPos += strlen(pszNew) - strlen(pszOld) + 1;
    }
    return strContent;
}

void IR_init(VexControl& vc) {
    tr_begin_run = clock();
    if (!TR_initdone) {
        Func_Map_Init();
        LibVEX_Init(&failure_exit, &_vex_log_bytes, 0/*debuglevel*/, &vc);
        TR_initdone = True;

        //for (int i = 0; i < 257; i++) fastalignD1[i] = (((((i)-1) & -8) + 8) >> 3) - 1;
        //for (int i = 0; i < 257; i++) fastalign[i] = (((((i)-1) & -8) + 8) >> 3);
        //for (int i = 0; i <= 64; i++) fastMask[i] = (1ull << i) - 1; fastMask[64] = -1ULL;
        //for (int i = 0; i <= 64; i++) fastMaskI1[i] = (1ull << (i + 1)) - 1; fastMaskI1[63] = -1ULL; fastMaskI1[64] = -1ULL;
        //for (int i = 0; i <= 7; i++) fastMaskB[i] = (1ull << (i << 3)) - 1; fastMaskB[8] = -1ULL;
        //for (int i = 0; i <= 7; i++) fastMaskBI1[i] = (1ull << ((i + 1) << 3)) - 1; fastMaskBI1[7] = -1ULL;
        //for (int i = 0; i <= 64; i++) fastMaskReverse[i] = ~fastMask[i];
        //for (int i = 0; i <= 64; i++) fastMaskReverseI1[i] = ~fastMaskI1[i];

    }
}


int eval_all(std::deque<tval>& result, z3::solver& solv, Z3_ast _exp) {
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
            std::cout << re << std::endl;
            if (re.is_numeral_u64(realu64)){
                result.emplace_back(tval(ctx, realu64, nbits));
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
}

//-1 err. 0 false. 1 true. 2 false || true.
int eval_all_bool(z3::solver& solv, Z3_ast _exp) {
    int ret = -1; 
    Z3_decl_kind bool_L, bool_R;
    z3::context& ctx = solv.ctx();
    z3::expr exp(ctx, _exp);

    //std::cout << exp << std::endl;
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
        z3::expr e1 = m1.eval(exp);
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
}









template<typename THword>
z3::expr StateMEM<THword>::idx2Value(Addr64 base, Z3_ast idx)
{
    z3::expr result = m_state.m_vctx.idx2value(m_state, base, idx);
    if ((Z3_ast)result) {
        return result;
    }
    result = crypto_finder(m_state, base, idx);
    return result;
}

template <typename THword> State<THword>::State(vex_context<THword>& vctx, THword gse, Bool _need_record) :
    Kernel(vctx),
    m_vctx(vctx),
    solv(m_ctx),
    mem(vctx, *this, solv, m_ctx, need_record),
    irvex(vctx, mem, vctx.gguest()),
    regs(m_ctx, need_record), 
    need_record(_need_record),
    m_status(NewState),
    m_jump_kd(Ijk_Boring),
    m_delta(0),
    m_z3_bv_const_n(0),
    m_InvokStack(),
    branch(*this)
{
    vctx.set_top_state(this);
    VexControl vc;
    LibVEX_default_VexControl(&vc);
    vc.iropt_verbosity = 0;
    vc.iropt_level = info().giropt_level();
#warning "whate is iropt_unroll_thresh"
    vc.iropt_unroll_thresh = 0;
    vc.guest_max_insns = info().gmax_insns();
    //vc.guest_chase_thresh = 0;   
    vc.guest_chase = True; //不许追赶
    vc.iropt_register_updates_default = info().gRegisterUpdates();
    IR_init(vc);
    
    read_mem_dump(info().gbin());
    if (gse)
        guest_start_ep = gse;
    else {
        guest_start_ep = regs.get<THword>(info().gRegsIpOffset()).tor();
    }
    guest_start = guest_start_ep;


    /*auto _TraceIrAddrress = info().doc_debug->FirstChildElement("TraceIrAddrress");
    if (_TraceIrAddrress) {
        for (auto ta = _TraceIrAddrress->FirstChildElement(); ta; ta = ta->NextSiblingElement()) {
            ULong addr; TRControlFlags flag;
            sscanf(ta->Attribute("addr"), "%llx", &addr);
            sscanf(ta->Attribute("cflag"), "%llx", &flag);
            vctx.hook_add(addr, nullptr, flag);
        }
    }*/

};


template <typename THword> State<THword>::State(State<THword>* father_state, THword gse) :
    Kernel(*father_state),
    m_vctx(father_state->m_vctx),
    mem(*this, solv, m_ctx, father_state->mem, father_state->need_record),
    irvex(m_vctx, mem, m_vctx.gguest()),
    guest_start_ep(gse),
    guest_start(guest_start_ep), 
    solv(m_ctx, father_state->solv,  z3::solver::translate{}),
    regs(father_state->regs, m_ctx, father_state->need_record),
    need_record(father_state->need_record),
    m_status(NewState),
    m_jump_kd(Ijk_Boring),
    m_delta(0),
    m_z3_bv_const_n(father_state->m_z3_bv_const_n),
    m_InvokStack(father_state->m_InvokStack),
    branch(*this, father_state->branch)
{

};




template <typename THword> State<THword>::~State() {
    if (m_dirty_vex_mode) {
        //dirty_context_del<THword>(m_dctx);
    }
    for (auto b : branch) {
        delete b;
    }
}

template<typename THword>
InvocationStack<THword>::operator std::string() const {
    std::string ret;
    char buff[100];
    UInt size = guest_call_stack.size();
    auto gcs = guest_call_stack.rbegin();
    auto gs = guest_stack.rbegin();
    for (UInt idx = 0; idx < size; idx++) {
        sprintf_s(buff, sizeof(buff), "0x%-16x :: 0x%-16x\n", *gcs, *gs);
        ret.append(buff);
        gcs++;
        gs++;
    }
    return ret;
}

template <typename THword>
State<THword>::operator std::string() const{
    std::string str;
    char hex[30];
    std::string strContent;
    

    str.append("\n#entry:");
    snprintf(hex, sizeof(hex),  "%llx", (size_t)guest_start_ep);
    strContent.assign(hex);
    str.append(strContent);
    str.append(" end:");
    snprintf(hex, sizeof(hex),  "%llx ", (size_t)guest_start);
    strContent.assign(hex);
    str.append(strContent);

    switch (m_status) {
    case NewState:str.append("NewState "); break;
    case Running:str.append("Running "); break;
    case Fork:str.append("Fork "); break;
    case Death:str.append("Death "); break;
    case Exit:str.append("Exit "); break;
    default:
        snprintf(hex, sizeof(hex),  "%d ", m_status);
        strContent.assign(hex);
        str.append(strContent); break;
    }

    str.append(" #child{\n");
    if (branch.empty()) {
        switch (m_status) {
        case NewState:str.append("NewState "); break;
        case Running:str.append("Running "); break;
        case Fork:str.append("Fork "); break;
        case Death:str.append("Death "); break;
        case Exit:str.append("Exit "); break;
        default:
            snprintf(hex, sizeof(hex),  "status:%d ", m_status);
            strContent.assign(hex);
            str.append(strContent); break;
        }
        snprintf(hex, sizeof(hex),  "%llx    \n}\n ", (size_t)guest_start);
        strContent.assign(hex);
        str.append(strContent);
        return str;
    }
    else {
        for (auto state : branch) {
            std::string child = *state;
            str.append(replace(child.c_str(), "\n", "\n   >"));
        }
    }
    str.append("\n}\n");
    return str;
}

template <typename THword>
tval State<THword>::mk_int_const(UShort nbit) {
    std::unique_lock<std::mutex> lock(m_state_lock);
    auto res = m_z3_bv_const_n++;
    char buff[20];
#ifdef _MSC_VER
    sprintf_s(buff, sizeof(buff), "p_%d", res);
#else
    snprintf(buff, sizeof(buff), "p_%d", res);
#endif
    return tval(m_ctx, m_ctx.bv_const(buff, nbit), Z3_BV_SORT, nbit);
}

template <typename THword>
tval State<THword>::mk_int_const(UShort n, UShort nbit) {
    char buff[20];
#ifdef _MSC_VER
    sprintf_s(buff, sizeof(buff), "p_%d", n);
#else
    snprintf(buff, sizeof(buff), "p_%d", n);
#endif
    return  tval(m_ctx, m_ctx.bv_const(buff, nbit), Z3_BV_SORT, nbit);
}

template <typename THword>
UInt State<THword>::getStr(std::stringstream& st, THword addr)
{
    UInt p = 0;
    while (True) {
        auto b = mem.template load<Ity_I8>(addr++);
        if (b.real()) {
            p++;
            st << (UChar)b.tor();
            if(!(UChar)b.tor()) return -1;
        }
        else {
            return p;
        }
    }
    return -1u;
}



template<typename THword>
tval TR::State<THword>::dirty_call(IRCallee* cee, IRExpr** exp_args, IRType ty)
{
    //getDirtyVexCtx();
    //dirty_ccall<THword>(m_dctx, cee, exp_args);
    //return dirty_result<THword>(m_dctx, ty);
}

template<typename THword>
tval TR::State<THword>::dirty_call(const HChar* name, void* func, std::initializer_list<rsval<Addr64>> parms, IRType ty)
{

    ctx64 v(VexArchAMD64, "");
    TR::EmuEnvironment emu_ev(v, mem, VexArchAMD64);
    IRSB* bb = emu_ev.translate_front(mem, (Addr)func);

    //getDirtyVexCtx();
    //dirty_call_np<THword>(m_dctx, name, func, parms);
    //return dirty_result<THword>(m_dctx, ty);
}



TR::TRsolver::TRsolver(z3::context& c)
    :
#if 1
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
    z3::tactic t_tactic(z3::with(z3::tactic(c, "simplify"), t_params) &
        z3::tactic(c, "sat") &
        z3::tactic(c, "solve-eqs") &
        z3::tactic(c, "bit-blast") &
        z3::tactic(c, "smt")
        &
        z3::tactic(c, "factor") &
        z3::tactic(c, "bv1-blast") &
       // z3::tactic(c, "qe-sat") &
        z3::tactic(c, "ctx-solver-simplify") &
        z3::tactic(c, "nla2bv") &
        z3::tactic(c, "symmetry-reduce")
    );
    return t_tactic.mk_solver();
}


typedef tval(*Z3_Function6)(tval&, tval&, tval&, tval&, tval&, tval&);
typedef tval(*Z3_Function5)(tval&, tval&, tval&, tval&, tval&);
typedef tval(*Z3_Function4)(tval&, tval&, tval&, tval&);
typedef tval(*Z3_Function3)(tval&, tval&, tval&);
typedef tval(*Z3_Function2)(tval&, tval&);
typedef tval(*Z3_Function1)(tval&);

typedef ULong(*Function_32_6)(UInt, UInt, UInt, UInt, UInt, UInt);
typedef ULong(*Function_32_5)(UInt, UInt, UInt, UInt, UInt);
typedef ULong(*Function_32_4)(UInt, UInt, UInt, UInt);
typedef ULong(*Function_32_3)(UInt, UInt, UInt);
typedef ULong(*Function_32_2)(UInt, UInt);
typedef ULong(*Function_32_1)(UInt);
typedef ULong(*Function_32_0)();

typedef ULong(*Function_64_6)(ULong, ULong, ULong, ULong, ULong, ULong);
typedef ULong(*Function_64_5)(ULong, ULong, ULong, ULong, ULong);
typedef ULong(*Function_64_4)(ULong, ULong, ULong, ULong);
typedef ULong(*Function_64_3)(ULong, ULong, ULong);
typedef ULong(*Function_64_2)(ULong, ULong);
typedef ULong(*Function_64_1)(ULong);
typedef ULong(*Function_64_0)();


#define CDFCHECK(arg0)\
if (arg0.symb()) {\
    z3_mode = True;\
    if (!cptr) { return dirty_call(cee, exp_args, ty); };\
}

template<>
tval State<Addr32>::CCall(IRCallee *cee, IRExpr **exp_args, IRType ty)
{
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return tval(m_ctx, ((Function_32_0)(cee->addr))(), bitn);
    void* cptr = funcDict(cee->addr);
    if (cptr == DIRTY_CALL_MAGIC) { 
        return dirty_call(cee, exp_args, ty);
    }
    tval arg0 = tIRExpr(exp_args[0]); CDFCHECK(arg0);
    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(cptr))(arg0) : tval(m_ctx, ((Function_32_1)(cee->addr))(arg0), bitn);
    tval arg1 = tIRExpr(exp_args[1]); CDFCHECK(arg1);
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(cptr))(arg0, arg1) : tval(m_ctx, ((Function_32_2)(cee->addr))(arg0, arg1), bitn);
    tval arg2 = tIRExpr(exp_args[2]); CDFCHECK(arg2);
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(cptr))(arg0, arg1, arg2) : tval(m_ctx, ((Function_32_3)(cee->addr))(arg0, arg1, arg2), bitn);
    tval arg3 = tIRExpr(exp_args[3]); CDFCHECK(arg3);
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(cptr))(arg0, arg1, arg2, arg3) : tval(m_ctx, ((Function_32_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    tval arg4 = tIRExpr(exp_args[4]); CDFCHECK(arg4);
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4) : tval(m_ctx, ((Function_32_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    tval arg5 = tIRExpr(exp_args[5]); CDFCHECK(arg5);
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5) : tval(m_ctx, ((Function_32_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
    VPANIC("not support");
}



template<>
tval State<Addr64>::CCall(IRCallee* cee, IRExpr** exp_args, IRType ty)
{
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return tval(m_ctx, ((Function_64_0)(cee->addr))(), bitn);

    void* cptr = funcDict(cee->addr); if (cptr == DIRTY_CALL_MAGIC) {
        return dirty_call(cee, exp_args, ty);
    }
    tval arg0 = tIRExpr(exp_args[0]); CDFCHECK(arg0);
    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(cptr))(arg0) : tval(m_ctx, ((Function_64_1)(cee->addr))(arg0), bitn);
    tval arg1 = tIRExpr(exp_args[1]); CDFCHECK(arg1);
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(cptr))(arg0, arg1) : tval(m_ctx, ((Function_64_2)(cee->addr))(arg0, arg1), bitn);
    tval arg2 = tIRExpr(exp_args[2]); CDFCHECK(arg2);
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(cptr))(arg0, arg1, arg2) : tval(m_ctx, ((Function_64_3)(cee->addr))(arg0, arg1, arg2), bitn);
    tval arg3 = tIRExpr(exp_args[3]); CDFCHECK(arg3);
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(cptr))(arg0, arg1, arg2, arg3) : tval(m_ctx, ((Function_64_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    tval arg4 = tIRExpr(exp_args[4]); CDFCHECK(arg4);
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4) : tval(m_ctx, ((Function_64_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    tval arg5 = tIRExpr(exp_args[5]); CDFCHECK(arg5);
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5) : tval(m_ctx, ((Function_64_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
    VPANIC("not support");
}
#undef CDFCHECK

template <typename THword>
void State<THword>::read_mem_dump(const char  *filename)
{
    struct memdump {
        unsigned long long nameoffset;
        unsigned long long address;
        unsigned long long length;
        unsigned long long dataoffset;
    }buf;
    if (!filename) return;
    std::ifstream infile;
    infile.open(filename, std::ios::binary);
    if (!infile.is_open()) {
        if (filename[0] == 0) { return; }
        std::cerr << filename << "not exit/n" << std::endl; return;
    }
    unsigned long long length, err, name_start_offset, name_end_offset, need_write_size = 0, write_count = 0;
    infile.seekg(0, std::ios::beg);
    infile.read((char*)&length, 8);
    infile.seekg(24, std::ios::beg);
    name_start_offset = length;
    infile.read((char*)&name_end_offset, 8);
    length /= 32;
    char* name_buff = (char*)malloc(name_end_offset - name_start_offset);
    infile.seekg(name_start_offset, std::ios::beg);
    infile.read(name_buff, name_end_offset - name_start_offset);
    infile.seekg(0, std::ios::beg);
    char *name;
    printf("Initializing Virtual Memory\n/------------------------------+--------------------+--------------------+------------\\\n");
    printf("|              SN              |         VA         |         FOA        |     LEN    |\n");
    printf("+------------------------------+--------------------+--------------------+------------+\n");
                                               \
    LARGE_INTEGER   freq = { 0 };                                                                                    
    LARGE_INTEGER   beginPerformanceCount = { 0 };                                                                   
    LARGE_INTEGER   closePerformanceCount = { 0 };                                                                   
    QueryPerformanceFrequency(&freq);                                                                                
    QueryPerformanceCounter(&beginPerformanceCount);
    for (unsigned int segnum = 0; segnum < length; segnum++) {
        infile.read((char*)&buf, 32);
        char *data = (char *)malloc(buf.length);
        std::streampos fp = infile.tellg();
        infile.seekg(buf.dataoffset, std::ios::beg);
        infile.read(data, buf.length);
        name = &name_buff[buf.nameoffset - name_start_offset];
        if (GET8(name)== 0x7265747369676572) {
#if 0
            printf("name:%18s address:%016llx data offset:%010llx length:%010llx\n", name, buf.address, buf.dataoffset, buf.length);
#endif
            memcpy((regs.m_bytes + buf.address), data, buf.length);
        }else {
            printf("| %-28s |  %16llx  |  %16llx  | %10llx |\n", name, buf.address, buf.dataoffset, buf.length);
            if (err = mem.map(buf.address, buf.length))
                printf("warning %s had maped before length: %llx\n", name, err);
            need_write_size += buf.length;
            write_count += mem.write_bytes(buf.address, buf.length,(unsigned char*) data);
        }
        infile.seekg(fp);
        free(data);
    }
    printf("\\-------------------------------------------------------------------------------------/\n");
    QueryPerformanceCounter(&closePerformanceCount);
    printf(
        "Spend time in:   %16lf s.\n"
        "Need to write    %16lf MByte.\n"
        "Actually written %16lf MByte\n", (double)(closePerformanceCount.QuadPart - beginPerformanceCount.QuadPart) / freq.QuadPart, ((double)need_write_size) / 0x100000,((double)write_count)/0x100000);
    free(name_buff);
    infile.close();
}

template <typename THword>
inline tval State<THword>::ILGop(IRLoadG *lg) {
    switch (lg->cvt) {
    case ILGop_IdentV128:{ return mem.Iex_Load(tIRExpr(lg->addr), Ity_V128);            }
    case ILGop_Ident64:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I64 );            }
    case ILGop_Ident32:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I32 );            }
    case ILGop_16Uto32:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I16 ).zext(16);   }
    case ILGop_16Sto32:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I16 ).sext(16);   }
    case ILGop_8Uto32:   { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I8  ).zext(8);    }
    case ILGop_8Sto32:   { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I8  ).sext(8);    }
    case ILGop_INVALID:
    default: VPANIC("ppIRLoadGOp");
    }
}

template <typename THword>
tval State<THword>::tIRExpr(IRExpr* e)
{
    switch (e->tag) {
    case Iex_Get: { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
    case Iex_RdTmp: { return irvex[e->Iex.RdTmp.tmp]; }
    case Iex_Unop: { return tUnop(e->Iex.Unop.op, tIRExpr(e->Iex.Unop.arg)); }
    case Iex_Binop: { return tBinop(e->Iex.Binop.op, tIRExpr(e->Iex.Binop.arg1), tIRExpr(e->Iex.Binop.arg2)); }
    case Iex_Triop: { return tTriop(e->Iex.Triop.details->op, tIRExpr(e->Iex.Triop.details->arg1), tIRExpr(e->Iex.Triop.details->arg2), tIRExpr(e->Iex.Triop.details->arg3)); }
    case Iex_Qop: { return tQop(e->Iex.Qop.details->op, tIRExpr(e->Iex.Qop.details->arg1), tIRExpr(e->Iex.Qop.details->arg2), tIRExpr(e->Iex.Qop.details->arg3), tIRExpr(e->Iex.Qop.details->arg4)); }
    case Iex_Load: { return mem.Iex_Load(tIRExpr(e->Iex.Load.addr), e->Iex.Get.ty); }
    case Iex_Const: { return tval(m_ctx, e->Iex.Const.con); }
    case Iex_ITE: {
        auto cond = tIRExpr(e->Iex.ITE.cond).tobool();
        if (cond.real()) {
            if (cond.tor())
                return tIRExpr(e->Iex.ITE.iftrue);
            else
                return tIRExpr(e->Iex.ITE.iffalse);
        }
        else {
            return ite(cond.tos(), tIRExpr(e->Iex.ITE.iftrue), tIRExpr(e->Iex.ITE.iffalse));
        }
    }
    case Iex_CCall: { return CCall(e->Iex.CCall.cee, e->Iex.CCall.args, e->Iex.CCall.retty); }
    case Iex_GetI: {
        auto ix = tIRExpr(e->Iex.GetI.ix);   /*  [e->Iex.GetI.ix, e->Iex.GetI.bias];  */
        assert(ix.real());
        return regs.Iex_Get(e->Iex.GetI.descr->base + (((UInt)(e->Iex.GetI.bias + (int)(ix))) % e->Iex.GetI.descr->nElems)*ty2length(e->Iex.GetI.descr->elemTy), e->Iex.GetI.descr->elemTy);
    };
    case Iex_GSPTR: { /*return tval(m_ctx, getGSPTR());*/  };
    case Iex_VECRET:
    case Iex_Binder:
    default:
        vex_printf("tIRExpr error:  %d", e->tag);
        VPANIC("not support");
    }
}

template<typename THword>
void TR::State<THword>::vex_push(const rsval<THword>& v)
{
    rsval<THword> sp = regs.get<THword>(m_vctx.gRegsSpOffset()) - sizeof(THword);
    regs.set(m_vctx.gRegsSpOffset(), sp);
    mem.store(sp, v);
}

template<typename THword>
rsval<THword> TR::State<THword>::vex_pop()
{
    rsval<THword> sp = regs.get<THword>(m_vctx.gRegsSpOffset());
    regs.set(m_vctx.gRegsSpOffset(), sp + 0x4u);
    return mem.load<THword>(sp);
}

template<typename THword>
rsval<THword> TR::State<THword>::vex_stack_get(int n)
{
    rsval<THword> sp = regs.get<THword>(m_vctx.gRegsSpOffset());
    return mem.load<THword>(sp + (THword)(n * sizeof(THword)));
}




template <typename THword>
bool State<THword>::vex_start() {
    Hook_struct hs;

    IRSB* irsb = nullptr;
    rsbool fork_guard(m_ctx, false);
    bool call_stack_is_empty = false;

    if UNLIKELY(jump_kd() != Ijk_Boring) {
        m_status = Ijk_call(jump_kd());
        set_jump_kd(Ijk_Boring);
        if (m_status != Running) {
            goto EXIT;
        }
    }

    if UNLIKELY(m_delta) {
        guest_start = guest_start + m_delta;
        m_delta = 0;
    }


    for (;;) {
    For_Begin:

        if UNLIKELY(m_vctx.get_hook(hs, guest_start)) {
        deal_bkp:
            m_status = _call_back_hook(hs);
            if UNLIKELY(m_status != Running) {
                goto EXIT;
            }
            if UNLIKELY(m_delta) {
                guest_start = guest_start + m_delta;
                m_delta = 0;
                goto For_Begin;
            }
        }
        irsb = irvex.translate_front(mem, guest_start);;
        traceIRSB(irsb);
        IRStmt* s = irsb->stmts[0];
        for (UInt stmtn = 0; stmtn < irsb->stmts_used;
            traceIRStmtEnd(s),
            s = irsb->stmts[++stmtn])
        {
            switch (s->tag) {
            case Ist_Put: { regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
            case Ist_Store: { mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; };
            case Ist_WrTmp: { irvex[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data); break; };
            case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
                std::unique_lock<std::mutex> lock(m_state_lock);
                IRCAS cas = *(s->Ist.CAS.details);
                tval addr = tIRExpr(cas.addr);//r10.value
                tval expdLo = tIRExpr(cas.expdLo);
                tval dataLo = tIRExpr(cas.dataLo);
                if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
                    tval expdHi = tIRExpr(cas.expdHi);
                    tval dataHi = tIRExpr(cas.dataHi);
                    irvex[cas.oldHi] = mem.Iex_Load(addr, expdLo.nbits());
                    irvex[cas.oldLo] = mem.Iex_Load(addr, expdLo.nbits());
                    mem.Ist_Store(addr, dataLo);
                    mem.Ist_Store(tval(addr.tors<false, wide>() + (dataLo.nbits() >> 3)), dataHi);
                }
                else {//single
                    irvex[cas.oldLo] = mem.Iex_Load(addr, expdLo.nbits());
                    mem.Ist_Store(addr, dataLo);
                }
                break;
            }
            case Ist_Exit: {
                rsbool guard = tIRExpr(s->Ist.Exit.guard).tobool();
                if LIKELY(guard.real()) {
                    if LIKELY(guard.tor()) {
                    Exit_guard_true:
                        if (s->Ist.Exit.jk != Ijk_Boring)
                        {
                            //ppIRSB(irsb);
                            m_status = Ijk_call(s->Ist.Exit.jk);
                            if (m_status != Running) {
                                goto EXIT;
                            }
                            if (m_delta) {
                                guest_start = guest_start + m_delta;
                                m_delta = 0;
                                goto For_Begin;
                            }
                            guest_start = s->Ist.Exit.dst->Ico.U64;
                        }
                        else {
                            guest_start = s->Ist.Exit.dst->Ico.U64;
                            goto For_Begin;
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
                        fork_guard = guard;
                        if (s->Ist.Exit.jk == Ijk_Boring) {
                            m_tmp_branch.push_back(BTS(*this, s->Ist.Exit.dst->Ico.U64, fork_guard));
                            break;
                        }
                        if (s->Ist.Exit.jk >= Ijk_SigILL && s->Ist.Exit.jk <= Ijk_SigFPE_IntOvf) {
                            m_tmp_branch.push_back(BTS(*this, s->Ist.Exit.dst->Ico.U64, fork_guard));
                            m_tmp_branch.back().set_jump_kd(s->Ist.Exit.jk);
                            break;
                        }
                        m_status = Fork;
                    }
                }
                break;
            }
            case Ist_NoOp: break;
            case Ist_IMark: {
                if UNLIKELY(m_status == Fork) {
                    m_tmp_branch.push_back(BTS(*this, (THword)s->Ist.IMark.addr, !fork_guard));
                    goto EXIT;
                }
                guest_start = (THword)s->Ist.IMark.addr;
                if UNLIKELY(irvex.check()) {
                    goto For_Begin;// fresh changed block
                }
                break;
            };
            case Ist_AbiHint: { //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
                tval nia = tIRExpr(s->Ist.AbiHint.nia);
                tval bp = regs.get<THword>(m_vctx.gRegsBpOffset());
                traceInvoke(nia, bp);
                m_InvokStack.push(nia, bp);
                break;
            }
            case Ist_PutI: {
                // PutI(840:8xI8)[t10,-1]
                // 840:arr->base
                // 8x :arr->nElems
                // I8 :arr->elemTy
                // t10:ix
                // -1 :e->Iex.GetI.bias
                auto ix = tIRExpr(s->Ist.PutI.details->ix);
                if (ix.real()) {
                    regs.Ist_Put(
                        s->Ist.PutI.details->descr->base + (((UInt)((s->Ist.PutI.details->bias + (int)(ix)))) % s->Ist.PutI.details->descr->nElems) * ty2length(s->Ist.PutI.details->descr->elemTy),
                        tIRExpr(s->Ist.PutI.details->data)
                    );
                }
                else {
                    vassert(0);
                }
                break;
            }
            case Ist_Dirty: {
                traceIRStmtEnd(s);
                IRDirty* dirty = s->Ist.Dirty.details;
                rsbool guard = tIRExpr(dirty->guard).tobool();
                if UNLIKELY(guard.symb()) {
                    VPANIC("auto guard = m_state.tIRExpr(dirty->guard); symbolic");
                }
                if LIKELY(guard.tor()) {
                    //getDirtyVexCtx();
                    //dirty_run<THword>(m_dctx, dirty);
                    if (dirty->tmp != IRTemp_INVALID) {
                        //ir_temp[dirty->tmp] = dirty_result<THword>(m_dctx, typeOfIRTemp(irsb->tyenv, dirty->tmp));
                    }
                }
                break;// fresh changed block
            }
            case Ist_LoadG: {
                IRLoadG* lg = s->Ist.LoadG.details;
                auto guard = tIRExpr(lg->guard).tobool();
                if LIKELY(guard.real()) {
                    irvex[lg->dst] = (guard.tor()) ? ILGop(lg) : tIRExpr(lg->alt);
                }
                else {
                    irvex[lg->dst] = ite(guard.tos(), ILGop(lg), tIRExpr(lg->alt));
                }
                break;
            }
            case Ist_StoreG: {
                IRStoreG* sg = s->Ist.StoreG.details;
                auto guard = tIRExpr(sg->guard).tobool();
                if LIKELY(guard.real()) {
                    if (guard.tor())
                        mem.Ist_Store(tIRExpr(sg->addr), tIRExpr(sg->data));
                }
                else {
                    auto addr = tIRExpr(sg->addr);
                    auto data = tIRExpr(sg->data);
                    mem.Ist_Store(addr, ite(guard.tos(), mem.Iex_Load(addr, data.nbits()), data));
                }
                break;
            }
            case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/ {
                vex_printf("IR-");
                ppIRMBusEvent(s->Ist.MBE.event);
                break;
            }
            case Ist_LLSC:
            default: {
                ppIRSB(irsb);
                vex_printf("addr: %p what ppIRStmt %d\n", guest_start, s->tag);
                VPANIC("what ppIRStmt");
            }
            }
        }

        traceIrsbEnd(irsb);
        switch (irsb->jumpkind) {
        case Ijk_Ret: {
            if UNLIKELY(call_stack_is_empty || m_InvokStack.empty()) {
                if (!call_stack_is_empty) {
                    call_stack_is_empty = true;
                    std::cout << "call stack end :: " << std::hex << guest_start << std::endl;
                }
            }
            else {
                m_InvokStack.pop();
            }
            break;
        }
        case Ijk_Boring: break;
        case Ijk_Call: {
            auto next = tIRExpr(irsb->next).template tor<false, wide>();
            auto bp = regs.get<THword>(m_vctx.gRegsBpOffset()).tor();
            traceInvoke(next, bp);
            m_InvokStack.push(next, bp);
            break; 
        }
        case Ijk_SigTRAP: {
            //software backpoint
            // if (m_vctx.get_hook(hs, guest_start)) { goto deal_bkp; }
            m_status = Exception;
        }
        default: {
            m_status = Ijk_call(irsb->jumpkind);
            if UNLIKELY(m_status != Running) {
                goto EXIT;
            }
            if UNLIKELY(m_delta) {
                guest_start = guest_start + m_delta;
                m_delta = 0;
                goto For_Begin;
            }
        }
        };
    Isb_next:
        sv::rsval<false, wide> next = tIRExpr(irsb->next).template tors<false, wide>();
        if UNLIKELY(m_status == Fork) {
            if LIKELY(next.real()) {
                m_tmp_branch.push_back(BTS(*this, (THword)next.tor(), !fork_guard));
            }
            else {
                std::deque<tval> result;
                Int eval_size = eval_all(result, solv, next.tos());
                if (eval_size <= 0) { 
                    throw Expt::SolverNoSolution("eval_size <= 0", solv);
                }
                else if (eval_size == 1) { 
                    guest_start = result[0].tor<false, wide>(); 
                }
                else {
                    for (auto re : result) {
                        auto GN = re.tor<false, wide>();//guest next ip
                        m_tmp_branch.push_back(BTS(*this, (THword)GN, !fork_guard, next == (THword)GN));
                    }
                }
            }
            goto EXIT;
        }

        if LIKELY(next.real()) {
            guest_start = next.tor();
        }
        else {
            std::deque<tval> result;
            Int eval_size = eval_all(result, solv, next.tos());
            if (eval_size <= 0) { 
                throw Expt::SolverNoSolution("eval_size <= 0", solv); 
            }
            else if (eval_size == 1) {
                guest_start = result[0].tor<false, wide>(); 
            }
            else {
                for (auto re : result) {
                    auto GN = re.tor<false, wide>();//guest next ip
                    m_tmp_branch.push_back(BTS(*this, (THword)GN, next == (THword)GN));
                    m_tmp_branch.back().set_jump_kd(irsb->jumpkind);
                }
                m_status = Fork;
                goto EXIT;
            }
        }
    };

EXIT:
    mem.set(nullptr);
    return true;
}

template <typename THword>
void State<THword>::start() {
    if (status() != NewState) {
        VPANIC("war: this->m_status != NewState");
    }
    m_status = Running;
    traceStart();
Begin_try:
    try {
        irvex.malloc_ir_buff(ctx());
        vex_start();
        irvex.free_ir_buff();
    }
    catch (Expt::ExceptionBase & error) {
        mem.set(nullptr);
        irvex.free_ir_buff();
        switch (error.errTag()) {
        case Expt::GuestRuntime_exception:
        case Expt::GuestMem_read_err:
        case Expt::GuestMem_write_err: {
            try {
                cpu_exception(error);
            }
            catch (Expt::ExceptionBase & cpu_exception_error) {
                std::cerr << "Usage issues or simulation software problems.\nError message:" << std::endl;
                std::cerr << error << std::endl;
                m_status = Death;
            }
            break;
        }
        case Expt::IR_failure_exit: {
            std::cerr << "Sorry This could be my design error. (BUG)\nError message:" << std::endl;
            std::cerr << error << std::endl;
            exit(1);
        }
        case Expt::Solver_no_solution: {
            std::cerr << " There is no solution to this problem. But this COULD BE my design error (BUG).\nError message:" << std::endl;
            std::cerr << error << std::endl;
            exit(1);
        }
        };
    }

    if (m_status == Exception) {
        m_status = Running;
        goto Begin_try;
    }

    traceFinish(); 
    return;
}


template <typename THword>
void State <THword>::branchGo()
{
    for(auto b : branch){
       m_vctx.pool().enqueue([b] {
            b->start();
            });
    }
}

template<typename THword>
class StateCmprsInterface {
    cmpr::StateType m_type;
    cmpr::CmprsContext<State<THword>, State_Tag>& m_ctx;
    State<THword>& m_state;
    sbool m_condition;
    static bool StateCompression(State<THword>& a, State<THword> const& next) {
        bool ret = a.m_InvokStack == next.m_InvokStack;// 压缩条件
        return ret && a.StateCompression(next);//支持扩展条件
    }

    static void StateCompressMkSymbol(State<THword>& a, State<THword> const& newState) {
        a.m_InvokStack = newState.m_InvokStack;// 使其满足压缩条件
        a.StateCompressMkSymbol(newState);//支持
    }

    std::vector<sbool> const & get_asserts() const { return m_state.solv.get_asserts(); };

public:
    StateCmprsInterface(
        cmpr::CmprsContext<State<THword>, State_Tag>& ctx,
        State<THword>& self,
        cmpr::StateType type
    ) :
        m_ctx(ctx), m_state(self), m_type(type), m_condition(m_ctx.ctx())
    { };

    cmpr::CmprsContext<State<THword>, State_Tag>& cctx() { return m_ctx; }
    cmpr::StateType type() { return m_type; };

    sbool const& get_assert() { 
        if (!(Z3_ast)m_condition) {
            m_condition = logic_and(get_asserts()).translate(m_ctx.ctx());
        }
        return m_condition;
    }

    void get_write_map(HASH_MAP<Addr64, bool>& record) {
        if (m_state.regs.getRecord()) {
            for (auto offset : *m_state.regs.getRecord()) {
                record[offset];
            }
        }
        for (auto mcm : m_state.mem.change_map()) {
            vassert(mcm.second->getRecord() != NULL);
            for (auto offset : *(mcm.second->getRecord())) {
                auto Address = mcm.first + offset;
                auto p = m_state.mem.get_mem_page(Address);
                vassert(p);
                vassert(p->get_user() == m_state.mem.get_user());
                vassert(Address > REGISTER_LEN);
                record[Address];
            }
        }
    }

    auto& branch() { return m_state.branch; };

    cmpr::StateType tag(State<THword>* son) {
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

    Int get_group_id(State<THword>* s) {
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

    PACK mem_Load(THword addr) {
        return m_state.mem.template load<Ity_I64>(addr).translate(m_ctx.ctx());
    }

    PACK reg_Get(UInt offset) {
        return m_state.regs.template get<Ity_I64>(offset).translate(m_ctx.ctx());
    }

    PACK read(THword addr) {
        if (addr < REGISTER_LEN) {
            return reg_Get(addr);
        }
        else {
            return mem_Load(addr);
        }
    }

    StateCmprsInterface<THword>* mk(State<THword>* son, cmpr::StateType tag) {
        //实际上少于4个case intel编译器会转为if
        switch (tag) {
        case cmpr::Fork_Node:return new cmpr::CmprsFork<StateCmprsInterface<THword>>(m_ctx, *son);
        case cmpr::Avoid_Node:return new cmpr::CmprsAvoid<StateCmprsInterface<THword>>(m_ctx, *son);
        case cmpr::Survive_Node:return new cmpr::CmprsSurvive<StateCmprsInterface<THword>>(m_ctx, *son);
        default:return new cmpr::CmprsTarget<StateCmprsInterface<THword>>(m_ctx, *son, tag);
        };

    }

    virtual bool has_survive() { return false; }
    virtual cmpr::CmprsFork<StateCmprsInterface<THword>>& get_fork_node() { VPANIC("???"); }
    virtual cmpr::CmprsTarget<StateCmprsInterface<THword>>& get_target_node() { VPANIC("???"); }
    virtual ~StateCmprsInterface() {};
};
#ifdef _DEBUG
#define PPCMPR
#endif
template <typename THword>
void State<THword>::compress(cmpr::CmprsContext<State<THword>, State_Tag>& ctx)
{
    cmpr::Compress<StateCmprsInterface<THword>, State<THword>, State_Tag> cmp(ctx, *this);
    if (!ctx.group().size()) { 
        return;
    }
    else if (ctx.group().size() > 1 || (ctx.group().size() == 1 && cmp.has_survive())) {

        for (cmpr::Compress<StateCmprsInterface<THword>, State<THword>, State_Tag>::Iterator::StateRes state : cmp) {
            State<THword>* nbranch = (State<THword>*)mkState(ctx.get_target_addr());
            tval condition = state.conditions().translate(*nbranch);
#ifdef  PPCMPR
            printf("%s\n", Z3_ast_to_string(condition, condition));
#endif //  _DEBUG
            nbranch->solv.add_assert(condition);
            HASH_MAP<Addr64, cmpr::GPMana> const& cm = state.changes();
            HASH_MAP<Addr64, cmpr::GPMana>::const_iterator itor = cm.begin();
            HASH_MAP<Addr64, cmpr::GPMana>::const_iterator end = cm.end();

            for (; itor != end; itor++) {
                Addr64 addr = itor->first;
                tval value = itor->second.get().translate(*nbranch);
#ifdef  PPCMPR
                printf("%p : {  %s  }\n", itor->first, Z3_ast_to_string(value, value));
#endif //  _DEBUG
                if (addr > REGISTER_LEN) {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    nbranch->mem.Ist_Store(addr, value);
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
        for (cmpr::Compress<StateCmprsInterface<THword>, State<THword>, State_Tag>::Iterator::StateRes state : cmp) {
            tval condition = state.conditions();
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
                tval value = itor->second.get();
#ifdef  PPCMPR
                printf("%p : {  %s  }\n", itor->first, Z3_ast_to_string(value, value));
#endif //  _DEBUG
                if (addr > REGISTER_LEN) {
#ifdef  PPCMPR
                    std::cout << std::hex << addr << value << std::endl;
#endif //  _DEBUG
                    mem.Ist_Store(addr, value);
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


template class TR::State<Addr32>;
template class TR::State<Addr64>;
template class TR::InvocationStack<Addr32>;
template class TR::InvocationStack<Addr64>;

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
    case Ity_INVALID: vex_printf("Ity_INVALID"); break;
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
    default:vpanic("ty2length");
    }
    return 0;
}

unsigned int ty2bit(IRType ty) {
    switch (ty) {
    case Ity_INVALID: vex_printf("Ity_INVALID"); break;
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
    default:vpanic("ty2length");
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
    default:vpanic("length2ty");
    }
    return Ity_INVALID;
}




unsigned int TRCurrentThreadId() {
    //teb+0x48
    uint32_t* teb = (uint32_t*)__readgsqword(0x30);
    return teb[0x12];
}


template<>
z3::expr crypto_finder( TR::State<Addr32>& s, Addr64 base, Z3_ast index) {
    if (c_crypto_find32) {
        return c_crypto_find32(s, base, index);
    }
    return z3::expr(s);
}

template<>
z3::expr crypto_finder( TR::State<Addr64>& s, Addr64 base, Z3_ast index) {
    if (c_crypto_find64) {
        return c_crypto_find64(s, base, index);
    }
    return z3::expr(s);
}

unsigned currentThreadId() {
    unsigned ThreadID;
#if defined(__APPLE__)
    asm("mov %%gs:0x00,%0" : "=r"(ThreadID));
#elif defined(__i386__)
    asm("mov %%gs:0x08,%0" : "=r"(ThreadID));
#elif defined(__x86_64__)
    asm("mov %%fs:0x10,%0" : "=r" (ThreadID));
#else
#error Unsupported architecture
#endif
    return ThreadID;
}


#undef CODEDEF1
#undef CODEDEF2

