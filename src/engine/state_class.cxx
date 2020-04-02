
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
#include <Windows.h>

using namespace TR;

template<typename ADDR>
z3::expr crypto_finder(TR::State<ADDR>& s, Addr64 base, Z3_ast index);

HMODULE hMod_crypto_analyzer = LoadLibraryA("libcrypto_analyzer.dll");

TR::vex_context<Addr32>::Hook_idx2Value c_crypto_find32 = (TR::vex_context<Addr32>::Hook_idx2Value)GetProcAddress(hMod_crypto_analyzer, "?crypto_finder32@@YA?AVexpr@z3@@AEAV?$State@I@TR@@IPEAU_Z3_ast@@@Z");;
TR::vex_context<Addr64>::Hook_idx2Value c_crypto_find64 = (TR::vex_context<Addr64>::Hook_idx2Value)GetProcAddress(hMod_crypto_analyzer, "?crypto_finder64@@YA?AVexpr@z3@@AEAV?$State@_K@TR@@_KPEAU_Z3_ast@@@Z");

static Bool TR_initdone;
static LARGE_INTEGER   freq_global = { 0 };
static LARGE_INTEGER   beginPerformanceCount_global = { 0 };
static LARGE_INTEGER   closePerformanceCount_global = { 0 };

//######################StateMEM START##############################

template class StateMEM<Addr32>;
template class StateMEM<Addr64>;

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
    QueryPerformanceFrequency(&freq_global);
    QueryPerformanceCounter(&beginPerformanceCount_global);
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


int eval_all(std::list<tval>& result, z3::solver& solv, Z3_ast nia) {
    //std::cout << nia << std::endl;
    //std::cout << state.solv.assertions() << std::endl;
    solv.push();
    //std::vector<Z3_model> mv;
    //mv.reserve(20);
    Z3_context ctx = solv.ctx();
    vassert(Z3_get_sort_kind(ctx, Z3_get_sort(ctx, nia)) == Z3_BV_SORT);
    for (int nway = 0; ; nway++) {
        Z3_lbool b = Z3_solver_check(ctx, solv);
        if (b == Z3_L_TRUE) {
            Z3_model m_model = Z3_solver_get_model(ctx, solv);
            Z3_model_inc_ref(ctx, m_model);
            // mv.emplace_back(m_model);
            Z3_ast r = 0;
            bool status = Z3_model_eval(ctx, m_model, nia, /*model_completion*/true, &r);
            result.emplace_back(tval(ctx, r));
            Z3_ast_kind rkind = Z3_get_ast_kind(ctx, r);
            if (rkind != Z3_NUMERAL_AST) {
                std::cout << rkind << Z3_ast_to_string(ctx, nia) << std::endl;
                std::cout << solv.assertions() << std::endl;
                vassert(0);
            }
            Z3_ast eq = Z3_mk_eq(ctx, nia, r);
            Z3_inc_ref(ctx, eq);
            Z3_ast neq = Z3_mk_not(ctx, eq);
            Z3_inc_ref(ctx, neq);
            Z3_solver_assert(ctx, solv, neq);
            Z3_dec_ref(ctx, eq);
            Z3_dec_ref(ctx, neq);

            Z3_model_dec_ref(ctx, m_model);
        }
        else {
            if (b == Z3_L_UNDEF){
                return -1;
            }
#if defined(OPSTR)
            for (auto s : result) std::cout << ", " << Z3_ast_to_string(ctx, s);
#endif
            solv.pop();
            //for (auto m : mv) Z3_model_dec_ref(ctx, m);
            return result.size();
        }
    }
}

template<typename ADDR>
z3::expr StateMEM<ADDR>::idx2Value(Addr64 base, Z3_ast idx)
{
    z3::expr result = m_state.m_vctx.idx2value(m_state, base, idx);
    if ((Z3_ast)result) {
        return result;
    }
    result = crypto_finder(m_state, base, idx);
    return result;
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
template <typename ADDR> State<ADDR>::State(vex_context<ADDR>& vctx, ADDR gse, Bool _need_record) :
    Kernel(vctx),
    m_vctx(vctx),
    solv(m_ctx),
    mem(vctx, *this, solv, m_ctx, need_record),
    regs(m_ctx, need_record), 
    need_record(_need_record),
    m_status(NewState),
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
    vc.iropt_unroll_thresh = 0;
    vc.guest_max_insns = info().gmax_insns();
    vc.guest_chase_thresh = 0;   //不许追赶
    vc.iropt_register_updates_default = info().gRegisterUpdates();
    IR_init(vc);
    
    read_mem_dump(info().gbin());
    if (gse)
        guest_start_ep = gse;
    else {
        guest_start_ep = regs.get<ADDR>(info().gRegsIpOffset());
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


template <typename ADDR> State<ADDR>::State(State<ADDR>*father_state, ADDR gse) :
    Kernel(*father_state),
    m_vctx(father_state->m_vctx),
    mem(*this, solv, m_ctx, father_state->mem, father_state->need_record),
    guest_start_ep(gse),
    guest_start(guest_start_ep), 
    solv(m_ctx, father_state->solv,  z3::solver::translate{}),
    regs(father_state->regs, m_ctx, father_state->need_record),
    need_record(father_state->need_record),
    m_status(NewState),
    m_delta(0),
    m_z3_bv_const_n(father_state->m_z3_bv_const_n),
    m_InvokStack(father_state->m_InvokStack),
    branch(*this, father_state->branch)
{

};




template <typename ADDR> State<ADDR>::~State() {
    if (m_dirty_vex_mode) {
        dirty_context_del<ADDR>(m_dctx);
    }
    for (auto b : branch) {
        delete b;
    }
}

template<typename ADDR>
InvocationStack<ADDR>::operator std::string() const {
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

template <typename ADDR>
State<ADDR>::operator std::string() const{
    std::string str;
    char hex[30];
    std::string strContent;
    

    str.append("\n#entry:");
    snprintf(hex, sizeof(hex),  "%llx", guest_start_ep);
    strContent.assign(hex);
    str.append(strContent);
    str.append(" end:");
    snprintf(hex, sizeof(hex),  "%llx ", guest_start);
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
        snprintf(hex, sizeof(hex),  "%llx    \n}\n ", guest_start);
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

template <typename ADDR>
tval State<ADDR>::mk_int_const(UShort nbit) {
    std::unique_lock<std::mutex> lock(m_state_lock);
    auto res = m_z3_bv_const_n++;
    char buff[20];
    sprintf_s(buff, sizeof(buff), "p_%d", res);
    return tval(m_ctx, m_ctx.bv_const(buff, nbit), nbit);
}

template <typename ADDR>
tval State<ADDR>::mk_int_const(UShort n, UShort nbit) {
    char buff[20];
    sprintf_s(buff, sizeof(buff), "p_%d", n);
    return  tval(m_ctx, m_ctx.bv_const(buff, nbit), nbit);
}

template <typename ADDR>
UInt State<ADDR>::getStr(std::stringstream& st, ADDR addr)
{
    UInt p = 0;
    while (True) {
        auto b = mem.load<Ity_I8>(addr++);
        if (b.real()) {
            p++;
            st << (UChar)b;
            if(!(UChar)b) return -1;
        }
        else {
            return p;
        }
    }
    return -1u;
}

template<typename ADDR>
DirtyCtx TR::State<ADDR>::getDirtyVexCtx()
{
    if (!m_dirty_vex_mode) {
        m_dirty_vex_mode = true;
        m_dctx = dirty_context(this);
    }
    return m_dctx;
}

template<typename ADDR>
tval TR::State<ADDR>::dirty_call(IRCallee* cee, IRExpr** exp_args, IRType ty)
{
    getDirtyVexCtx();
    dirty_ccall<ADDR>(m_dctx, cee, exp_args);
    return dirty_result<ADDR>(m_dctx, ty);
}

template<typename ADDR>
tval TR::State<ADDR>::dirty_call(const HChar* name, void* func, std::initializer_list<rsval<Addr64>> parms, IRType ty)
{
    getDirtyVexCtx();
    dirty_call_np<ADDR>(m_dctx, name, func, parms);
    return dirty_result<ADDR>(m_dctx, ty);
}



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

template <typename ADDR>
void State<ADDR>::read_mem_dump(const char  *filename)
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

template <typename ADDR>
inline tval State<ADDR>::ILGop(IRLoadG *lg) {
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

template <typename ADDR>
inline tval State<ADDR>::tIRExpr(IRExpr* e)
{
    switch (e->tag) {
    case Iex_Get: { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
    case Iex_RdTmp: { return m_ir_temp[e->Iex.RdTmp.tmp]; }
    case Iex_Unop: { return tUnop(e->Iex.Unop.op, tIRExpr(e->Iex.Unop.arg)); }
    case Iex_Binop: { return tBinop(e->Iex.Binop.op, tIRExpr(e->Iex.Binop.arg1), tIRExpr(e->Iex.Binop.arg2)); }
    case Iex_Triop: { return tTriop(e->Iex.Triop.details->op, tIRExpr(e->Iex.Triop.details->arg1), tIRExpr(e->Iex.Triop.details->arg2), tIRExpr(e->Iex.Triop.details->arg3)); }
    case Iex_Qop: { return tQop(e->Iex.Qop.details->op, tIRExpr(e->Iex.Qop.details->arg1), tIRExpr(e->Iex.Qop.details->arg2), tIRExpr(e->Iex.Qop.details->arg3), tIRExpr(e->Iex.Qop.details->arg4)); }
    case Iex_Load: { return mem.Iex_Load(tIRExpr(e->Iex.Load.addr), e->Iex.Get.ty); }
    case Iex_Const: { return tval(m_ctx, e->Iex.Const.con); }
    case Iex_ITE: {
       /* tval cond = tIRExpr(e->Iex.ITE.cond);
        return (cond.real()) ?
            ((UChar)cond & 0b1) ? tIRExpr(e->Iex.ITE.iftrue) : tIRExpr(e->Iex.ITE.iffalse)
            :
            tval(m_ctx, Z3_mk_ite(m_ctx, cond.toZ3Bool(), tIRExpr(e->Iex.ITE.iftrue), tIRExpr(e->Iex.ITE.iffalse)));*/
    }
    case Iex_CCall: { return CCall(e->Iex.CCall.cee, e->Iex.CCall.args, e->Iex.CCall.retty); }
    case Iex_GetI: {
        auto ix = tIRExpr(e->Iex.GetI.ix);   /*  [e->Iex.GetI.ix, e->Iex.GetI.bias];  */
        assert(ix.real());
        return regs.Iex_Get(e->Iex.GetI.descr->base + (((UInt)(e->Iex.GetI.bias + (int)(ix))) % e->Iex.GetI.descr->nElems)*ty2length(e->Iex.GetI.descr->elemTy), e->Iex.GetI.descr->elemTy);
    };
    case Iex_GSPTR: { return tval(m_ctx, getGSPTR());  };
    case Iex_VECRET:
    case Iex_Binder:
    default:
        vex_printf("tIRExpr error:  %d", e->tag);
        VPANIC("not support");
    }
}

template<typename ADDR>
void TR::State<ADDR>::vex_push(const rsval<ADDR>& v)
{
    rsval<ADDR> sp = regs.get<ADDR>(m_vctx.gRegsSpOffset()) - sizeof(ADDR);
    regs.set(m_vctx.gRegsSpOffset(), sp);
    mem.store(sp, v);
}

template<typename ADDR>
rsval<ADDR> TR::State<ADDR>::vex_pop()
{
    rsval<ADDR> sp = regs.get<ADDR>(m_vctx.gRegsSpOffset());
    regs.set(m_vctx.gRegsSpOffset(), sp + 0x4u);
    return mem.load<ADDR>(sp);
}

template<typename ADDR>
rsval<ADDR> TR::State<ADDR>::vex_stack_get(int n)
{
    rsval<ADDR> sp = regs.get<ADDR>(m_vctx.gRegsSpOffset());
    return mem.load<ADDR>(sp + (ADDR)(n * sizeof(ADDR)));
}

template <typename ADDR>
bool State<ADDR>::vex_start() {
    if (m_delta) {
        guest_start = guest_start + m_delta;
        m_delta = 0;
    }
    Hook_struct hs;
    EmuEnvironment<MAX_IRTEMP> emu(info(), mem);
    setTemp(emu);
    mem.set(&emu);
    IRSB* irsb = nullptr;
    State<ADDR>* newBranch = nullptr;
    bool call_stack_is_empty = false;

    if (m_vctx.get_hook(hs, guest_start)) { goto bkp_pass; }

    for (;;) {
    For_Begin:
        mem.set_double_page(guest_start, emu);
        emu.set_guest_bytes_addr(emu->t_page_addr, guest_start);
        VexRegisterUpdates pxControl;
        VexTranslateResult res;
        IRSB* irsb = LibVEX_FrontEnd(emu, &res, &pxControl, emu);;
        traceIRSB(irsb);
        goto For_Begin_NO_Trans;
    deal_bkp:
        {
            m_status = _call_back_hook(hs);
            if (m_status != Running) {
                goto EXIT;
            }
            if (m_delta) {
                guest_start = guest_start + m_delta;
                m_delta = 0;
                goto For_Begin;
            }
            else {
            bkp_pass:
                emu.set_guest_code_temp(mem, guest_start, hs);
                irsb = LibVEX_FrontEnd(emu, &res, &pxControl, emu);
                //ppIRSB(irsb);
            }
        }
    For_Begin_NO_Trans:
        IRStmt* s = irsb->stmts[0];
        for (UInt stmtn = 0; stmtn < irsb->stmts_used;
            traceIRStmtEnd(s),
            s = irsb->stmts[++stmtn])
        {
            switch (s->tag) {
            case Ist_Put: { regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
            case Ist_Store: { mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; };
            case Ist_WrTmp: { emu[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data); break; };
            case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
                std::unique_lock<std::mutex> lock(m_state_lock);
                IRCAS cas = *(s->Ist.CAS.details);
                tval addr = tIRExpr(cas.addr);//r10.value
                tval expdLo = tIRExpr(cas.expdLo);
                tval dataLo = tIRExpr(cas.dataLo);
                if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
                    tval expdHi = tIRExpr(cas.expdHi);
                    tval dataHi = tIRExpr(cas.dataHi);
                    emu[cas.oldHi] = mem.Iex_Load(addr, expdLo.nbits());
                    emu[cas.oldLo] = mem.Iex_Load(addr, expdLo.nbits());
                    mem.Ist_Store(addr, dataLo);
                    mem.Ist_Store(addr + (dataLo.nbits() >> 3), dataHi);
                }
                else {//single
                    emu[cas.oldLo] = mem.Iex_Load(addr, expdLo.nbits());
                    mem.Ist_Store(addr, dataLo);
                }
                break;
            }
            case Ist_Exit: {
                rsbool guard = tIRExpr(s->Ist.Exit.guard).tobool();
                if (guard.real()) {
                    if ((UChar)guard & 1) {
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
                    /*std::vector<tval> guard_result;
                    Int eval_size = eval_all(guard_result, solv, guard);
                    if (eval_size <= 0) {  throw Expt::SolverNoSolution("eval_size <= 0", solv); }
                    if (eval_size == 1) {
                        if (((UChar)guard_result[0].simplify()) & 1)
                            goto Exit_guard_true;
                    }
                    if (eval_size == 2) {
                        if (s->Ist.Exit.jk != Ijk_Boring) {
                            solv.add_assert(guard, False);
                        }
                        else {
                            vassert(s->Ist.Exit.jk == Ijk_Boring);
                            newBranch = (State<ADDR>*)mkState(s->Ist.Exit.dst->Ico.U64);
                            newBranch->solv.add_assert(guard);
                            m_status = Fork;
                        }
                    }*/
                }
                break;
            }
            case Ist_NoOp: break;
            case Ist_IMark: {
                if (m_status == Fork) {
                    State<ADDR>* prv = newBranch;
                    newBranch = (State<ADDR>*)mkState((ADDR)s->Ist.IMark.addr);
                    newBranch->solv.add_assert(!prv->solv.get_asserts()[0]);
                    goto EXIT;
                }
                guest_start = (ADDR)s->Ist.IMark.addr;
                if (emu.check()) {
                    goto For_Begin;// fresh changed block
                }
                break;
            };
            case Ist_AbiHint: { //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
                tval nia = tIRExpr(s->Ist.AbiHint.nia);
                tval bp = regs.get<ADDR>(m_vctx.gRegsBpOffset());
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
                if (guard.symb()) {
                    VPANIC("auto guard = m_state.tIRExpr(dirty->guard); symbolic");
                }
                if (((UChar)guard) & 1) {
                    getDirtyVexCtx();
                    dirty_run<ADDR>(m_dctx, dirty);
                    if (dirty->tmp != IRTemp_INVALID) {
                        emu[dirty->tmp] = dirty_result<ADDR>(m_dctx, typeOfIRTemp(irsb->tyenv, dirty->tmp));
                    }
                }
                break;// fresh changed block
            }
            case Ist_LoadG: {
                IRLoadG* lg = s->Ist.LoadG.details;
                auto guard = tIRExpr(lg->guard).tobool();
                if (guard.real()) {
                    emu[lg->dst] = (((UChar)guard)) ? ILGop(lg) : tIRExpr(lg->alt);
                }
                else {
                    //emu[lg->dst] = ite(guard, ILGop(lg), tIRExpr(lg->alt));
                }
                break;
            }
            case Ist_StoreG: {
                IRStoreG* sg = s->Ist.StoreG.details;
                auto guard = tIRExpr(sg->guard).tobool();
                if (guard.real()) {
                    if ((UChar)guard)
                        mem.Ist_Store(tIRExpr(sg->addr), tIRExpr(sg->data));
                }
                else {
                    auto addr = tIRExpr(sg->addr);
                    auto data = tIRExpr(sg->data);
                    //mem.Ist_Store(addr, ite(guard, mem.Iex_Load(addr, data.nbits()), data));
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
            if (call_stack_is_empty || m_InvokStack.empty()) {
                if (!call_stack_is_empty) {
                    call_stack_is_empty = true;
                    std::cout << "调用栈结束 :: " << std::hex << guest_start << std::endl;
                }
            }
            else {
                m_InvokStack.pop();
            }
            break;
        }
        case Ijk_Boring: break;
        case Ijk_Call: {
            auto next = tIRExpr(irsb->next);
            auto bp = regs.get<ADDR>(m_vctx.gRegsBpOffset());
            traceInvoke(next, bp);
            m_InvokStack.push(next, bp);
            break; 
        }
        case Ijk_SigTRAP: {
            //software backpoint
            if (m_vctx.get_hook(hs, guest_start)) { goto deal_bkp; }
            m_status = Exception;
        }
        default: {
            m_status = Ijk_call(irsb->jumpkind);
            if (m_status != Running) {
                goto EXIT;
            }
            if (m_delta) {
                guest_start = guest_start + m_delta;
                m_delta = 0;
                goto For_Begin;
            }
        }
        };
    Isb_next:
        tval next = tIRExpr(irsb->next);
        if (m_status == Fork) {

            State<ADDR>* prv = newBranch;
            const sbool& guard = prv->solv.get_asserts()[0];
            if (next.real()) {
                newBranch = (State<ADDR>*)mkState((ADDR)next);
                newBranch->solv.add_assert(!guard);
            }
            else {
                //std::vector<tval> result;
                //Int eval_size = eval_all(result, solv, next);
                //if (eval_size <= 0) { throw Expt::SolverNoSolution("eval_size <= 0", solv); }
                //else if (eval_size == 1) { guest_start = result[0].simplify(); }
                //else {
                //    for (auto re : result) {
                //        ADDR GN = re.simplify();//guest next ip
                //        newBranch = (State<ADDR>*)mkState((ADDR)GN);
                //        newBranch->solv.add_assert(guard, False);
                //        newBranch->solv.add_assert_eq(next, re);
                //    }
                //}
            }
            goto EXIT;
        }

        if (next.real()) {
            guest_start = next;
        }
        else {
            //std::vector<tval> result;
            //Int eval_size = eval_all(result, solv, next);
            //if (eval_size <= 0) { throw Expt::SolverNoSolution("eval_size <= 0", solv); }
            //else if (eval_size == 1) { guest_start = result[0].simplify(); }
            //else {
            //    for (auto re : result) {
            //        ADDR GN = re.simplify();//guest next ip
            //        newBranch = (State<ADDR>*)mkState((ADDR)GN);
            //        newBranch->solv.add_assert_eq(next, re);
            //    }
            //    m_status = Fork;
            //    goto EXIT;
            //}
        }
    };

EXIT:
    mem.set(nullptr);
    m_ir_temp = nullptr;
}

template <typename ADDR>
void State<ADDR>::start() {
    if (this->m_status != NewState) {
        std::cout <<"war: this->m_status != NewState"<< std::endl;
    }
    m_status = Running;
    traceStart();
Begin_try:
    try {
        vex_start();
    }
    catch (Expt::ExceptionBase & error) {
        mem.set(nullptr);
        m_ir_temp = nullptr;
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


template <typename ADDR>
void State <ADDR>::branchGo()
{
    for(auto b : branch){
       m_vctx.pool().enqueue([b] {
            b->start();
            });
    }
}

template<typename ADDR>
class StateCmprsInterface {
    cmpr::StateType m_type;
    cmpr::CmprsContext<State<ADDR>, State_Tag>& m_ctx;
    State<ADDR>& m_state;
    sbool m_condition;
    static bool StateCompression(State<ADDR>& a, State<ADDR> const& next) {
        bool ret = a.m_InvokStack == next.m_InvokStack;// 压缩条件
        return ret && a.StateCompression(next);//支持扩展条件
    }

    static void StateCompressMkSymbol(State<ADDR>& a, State<ADDR> const& newState) {
        a.m_InvokStack = newState.m_InvokStack;// 使其满足压缩条件
        a.StateCompressMkSymbol(newState);//支持
    }

    std::vector<sbool> const & get_asserts() const { return m_state.solv.get_asserts(); };

public:
    StateCmprsInterface(
        cmpr::CmprsContext<State<ADDR>, State_Tag>& ctx,
        State<ADDR>& self,
        cmpr::StateType type
    ) :
        m_ctx(ctx), m_state(self), m_type(type), m_condition(cmpr::logic_and(get_asserts()).translate(m_ctx.ctx()))
    { };

    cmpr::CmprsContext<State<ADDR>, State_Tag>& cctx() { return m_ctx; }
    cmpr::StateType type() { return m_type; };

    sbool const& get_assert() { return m_condition; }

    void get_write_map(std::hash_map<Addr64, bool>& record) {
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

    cmpr::StateType tag(State<ADDR>* son) {
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

    Int get_group_id(State<ADDR>* s) {
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

    PACK mem_Load(ADDR addr) {
        return m_state.mem.load<Ity_I64>(addr).translate(m_ctx.ctx());
    }

    PACK reg_Get(UInt offset) {
        return m_state.regs.get<Ity_I64>(offset).translate(m_ctx.ctx());
    }

    PACK read(ADDR addr) {
        if (addr < REGISTER_LEN) {
            return reg_Get(addr);
        }
        else {
            return mem_Load(addr);
        }
    }

    StateCmprsInterface<ADDR>* mk(State<ADDR>* son, cmpr::StateType tag) {
        //实际上少于4个case intel编译器会转为if
        switch (tag) {
        case cmpr::Fork_Node:return new cmpr::CmprsFork<StateCmprsInterface<ADDR>>(m_ctx, *son);
        case cmpr::Avoid_Node:return new cmpr::CmprsAvoid<StateCmprsInterface<ADDR>>(m_ctx, *son);
        case cmpr::Survive_Node:return new cmpr::CmprsSurvive<StateCmprsInterface<ADDR>>(m_ctx, *son);
        default:return new cmpr::CmprsTarget<StateCmprsInterface<ADDR>>(m_ctx, *son, tag);
        };

    }

    virtual bool has_survive() { return false; }
    virtual cmpr::CmprsFork<StateCmprsInterface<ADDR>>& get_fork_node() { VPANIC("???"); }
    virtual cmpr::CmprsTarget<StateCmprsInterface<ADDR>>& get_target_node() { VPANIC("???"); }
    virtual ~StateCmprsInterface() {};
};
#ifdef _DEBUG
#define PPCMPR
#endif
template <typename ADDR>
void State<ADDR>::compress(cmpr::CmprsContext<State<ADDR>, State_Tag>& ctx)
{
    cmpr::Compress<StateCmprsInterface<ADDR>, State<ADDR>, State_Tag> cmp(ctx, *this);
    if (!ctx.group().size()) { 
        return;
    }
    else if (ctx.group().size() > 1 || (ctx.group().size() == 1 && cmp.has_survive())) {

        for (cmpr::Compress<StateCmprsInterface<ADDR>, State<ADDR>, State_Tag>::Iterator::StateRes state : cmp) {
            State<ADDR>* nbranch = (State<ADDR>*)mkState(ctx.get_target_addr());
            tval condition = state.conditions().translate(*nbranch);
#ifdef  PPCMPR
            printf("%s\n", Z3_ast_to_string(condition, condition));
#endif //  _DEBUG
            nbranch->solv.add_assert(condition);
            std::hash_map<Addr64, cmpr::GPMana> const& cm = state.changes();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator itor = cm.begin();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator end = cm.end();

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
        for (cmpr::Compress<StateCmprsInterface<ADDR>, State<ADDR>, State_Tag>::Iterator::StateRes state : cmp) {
            tval condition = state.conditions();
#ifdef  PPCMPR
            printf("%s\n", Z3_ast_to_string(condition, condition));
#endif //  _DEBUG
            solv.add_assert(condition);
            std::hash_map<Addr64, cmpr::GPMana> const& cm = state.changes();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator itor = cm.begin();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator end = cm.end();
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


template TR::State<Addr32>;
template TR::State<Addr64>;
template TR::InvocationStack<Addr32>;
template TR::InvocationStack<Addr64>;

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



#define CODEDEF1(name)					 \
switch (length) {						 \
case 8:vex_printf((name)); break;		 \
default:goto none;						 \
}break;								     \


#define CODEDEF2(length,name)			\
switch ((length)) {						\
case 1:vex_printf((name)); break;		\
default:goto none;						\
}break;									


void tAMD64REGS(int offset, int length) {
    vex_printf("\t\t");
    switch (offset) {
    case 16:
        switch (length) {
        case 8:vex_printf("rax"); break;
        case 4:vex_printf("eax"); break;
        case 2:vex_printf(" ax"); break;
        case 1:vex_printf(" al"); break;
        default:goto none;
        }break;
        CODEDEF2(17, "ah");
    case 24:
        switch (length) {
        case 8:vex_printf("rcx"); break;
        case 4:vex_printf("ecx"); break;
        case 2:vex_printf(" cx"); break;
        case 1:vex_printf(" cl"); break;
        default:goto none;
        }break;
        CODEDEF2(25, "ch");
    case 32: vex_printf("rdx"); break;
        switch (length) {
        case 8:vex_printf("rdx"); break;
        case 4:vex_printf("edx"); break;
        case 2:vex_printf(" dx"); break;
        case 1:vex_printf(" dl"); break;
        default:goto none;
        }break;
        CODEDEF2(33, "dh");
    case 40: vex_printf("rbx"); break;
        switch (length) {
        case 8:vex_printf("rbx"); break;
        case 4:vex_printf("ebx"); break;
        case 2:vex_printf(" bx"); break;
        case 1:vex_printf(" bl"); break;
        default:goto none;
        }break;
    case 48: vex_printf("rsp"); break;
        switch (length) {
        case 8:vex_printf("rsp"); break;
        case 4:vex_printf("esp"); break;
        default:goto none;
        }break;
    case 56: vex_printf("rbp"); break;
        switch (length) {
        case 8:vex_printf("rbp"); break;
        case 4:vex_printf("ebp"); break;
        default:goto none;
        }break;
    case 64: vex_printf("rsi"); break;
        switch (length) {
        case 8:vex_printf("rsi"); break;
        case 4:vex_printf("esi"); break;
        case 2:vex_printf(" si"); break;
        case 1:vex_printf("sil"); break;
        default:goto none;
        }break;
        CODEDEF2(65, "sih");
    case 72: vex_printf("rdi"); break;
        switch (length) {
        case 8:vex_printf("rdi"); break;
        case 4:vex_printf("edi"); break;
        case 2:vex_printf(" di"); break;
        case 1:vex_printf(" dil"); break;
        default:goto none;
        }break;
        CODEDEF2(73, "dih");
    case 80: vex_printf("r8"); break;
    case 88: vex_printf("r9"); break;
    case 96: vex_printf("r10"); break;
    case 104: vex_printf("r11"); break;
    case 112: vex_printf("r12"); break;
    case 120: vex_printf("r13"); break;
    case 128: vex_printf("r14"); break;
    case 136: vex_printf("r15"); break;
    case 144: vex_printf("cc_op"); break;
    case 152: vex_printf("cc_dep1"); break;
    case 160: vex_printf("cc_dep2"); break;
    case 168: vex_printf("cc_ndep"); break;
    case 176: vex_printf("d"); break;
    case 184: vex_printf("rip"); break;
    case 192: vex_printf("ac"); break;
    case 200: vex_printf("id"); break;
    case 208: vex_printf("fs"); break;
    case 216: vex_printf("sseround"); break;
    case 224:
        switch (length) {
        case 32:vex_printf("ymm0"); break;
        case 16:vex_printf("xmm0"); break;
        default:vex_printf("ymm0"); break;
        }break;
    case 256:
        switch (length) {
        case 32:vex_printf("ymm1"); break;
        case 16:vex_printf("xmm1"); break;
        default:vex_printf("ymm1"); break;
        }break;
    case 288:
        switch (length) {
        case 32:vex_printf("ymm2"); break;
        case 16:vex_printf("xmm2"); break;
        default:vex_printf("ymm2"); break;
        }break;
    case 320:
        switch (length) {
        case 32:vex_printf("ymm3"); break;
        case 16:vex_printf("xmm3"); break;
        default:vex_printf("ymm3"); break;
        }break;
    case 352:
        switch (length) {
        case 32:vex_printf("ymm4"); break;
        case 16:vex_printf("xmm4"); break;
        default:vex_printf("ymm4"); break;
        }break;
    case 384:
        switch (length) {
        case 32:vex_printf("ymm5"); break;
        case 16:vex_printf("xmm5"); break;
        default:vex_printf("ymm5"); break;
        }break;
    case 416:
        switch (length) {
        case 32:vex_printf("ymm6"); break;
        case 16:vex_printf("xmm6"); break;
        default:vex_printf("ymm6"); break;
        }break;
    case 448:
        switch (length) {
        case 32:vex_printf("ymm7"); break;
        case 16:vex_printf("xmm7"); break;
        default:vex_printf("ymm7"); break;
        }break;
    case 480:
        switch (length) {
        case 32:vex_printf("ymm8"); break;
        case 16:vex_printf("xmm8"); break;
        default:vex_printf("ymm8"); break;
        }break;
    case 512:
        switch (length) {
        case 32:vex_printf("ymm9"); break;
        case 16:vex_printf("xmm9"); break;
        default:vex_printf("ymm9"); break;
        }break;
    case 544:
        switch (length) {
        case 32:vex_printf("ymm10"); break;
        case 16:vex_printf("xmm10"); break;
        default:vex_printf("ymm10"); break;
        }break;
    case 576:
        switch (length) {
        case 32:vex_printf("ymm11"); break;
        case 16:vex_printf("xmm11"); break;
        default:vex_printf("ymm11"); break;
        }break;
    case 608:
        switch (length) {
        case 32:vex_printf("ymm12"); break;
        case 16:vex_printf("xmm12"); break;
        default:vex_printf("ymm12"); break;
        }break;
    case 640:
        switch (length) {
        case 32:vex_printf("ymm13"); break;
        case 16:vex_printf("xmm13"); break;
        default:vex_printf("ymm13"); break;
        }break;
    case 672:
        switch (length) {
        case 32:vex_printf("ymm14"); break;
        case 16:vex_printf("xmm14"); break;
        default:vex_printf("ymm14"); break;
        }break;
    case 704:
        switch (length) {
        case 32:vex_printf("ymm15"); break;
        case 16:vex_printf("xmm15"); break;
        default:vex_printf("ymm15"); break;
        }break;
    case 736:
        switch (length) {
        case 32:vex_printf("ymm16"); break;
        case 16:vex_printf("xmm16"); break;
        default:vex_printf("ymm16"); break;
        }break;
    case 768: vex_printf("ftop"); break;
    case 776:
        switch (length) {
        case 64:vex_printf("fpreg"); break;
        case 8:vex_printf("mm0"); break;
        default:vex_printf("fpreg"); break;
        }break;
    case 784: CODEDEF1("mm1")
    case 792: CODEDEF1("mm2")
    case 800: CODEDEF1("mm3")
    case 808: CODEDEF1("mm4")
    case 816: CODEDEF1("mm5")
    case 824: CODEDEF1("mm6")
    case 832: CODEDEF1("mm7")
    case 840: CODEDEF1("fptag")
    case 848: CODEDEF1("fpround")
    case 856: CODEDEF1("fc3210")
    case 864: {
        switch (length) {
        case 4:vex_printf("emnote"); break;
        default:goto none;
        }break;
    }
    case 872: CODEDEF1("cmstart")
    case 880: CODEDEF1("cmlen")
    case 888: CODEDEF1("nraddr")
    case 904: CODEDEF1("gs")
    case 912: CODEDEF1("ip_at_syscall")
    default:goto none;
    }
    return;
none:
    vex_printf(" what regoffset = %d ", offset);
}


unsigned int TRCurrentThreadId() {
    return __readgsdword(0x30);
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


#undef CODEDEF1
#undef CODEDEF2

