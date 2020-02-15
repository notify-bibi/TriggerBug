﻿
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
#include "State_class.hpp"

#include "Z3_Target_Call/Z3_Target_Call.hpp"
#include "Z3_Target_Call/Guest_Helper.hpp"

thread_local Z3_context cmpr::thread_z3_ctx;

thread_local void* g_state = nullptr;
thread_local Pap    pap;
thread_local Addr64   guest_start_of_block = 0;
thread_local bool   is_dynamic_block = false;//Need to refresh IRSB memory?
thread_local UChar  ir_temp_trunk[MAX_IRTEMP * sizeof(Vns)];
thread_local VexTranslateArgs       vta_chunk;
thread_local VexGuestExtents        vge_chunk;

LARGE_INTEGER   freq_global = { 0 };
LARGE_INTEGER   beginPerformanceCount_global = { 0 };
LARGE_INTEGER   closePerformanceCount_global = { 0 };

typedef Vns (*Z3_Function6)(Vns &, Vns &, Vns &, Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function5)(Vns &, Vns &, Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function4)(Vns &, Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function3)(Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function2)(Vns &, Vns &);
typedef Vns (*Z3_Function1)(Vns &);



__m256i m32_fast[33];
__m256i m32_mask_reverse[33];

std::hash_map<Addr64, Hook_struct>                                Kernel::CallBackDict;
std::hash_map<Addr64/*static table base*/, TRtype::TableIdx_CB>   Kernel::TableIdxDict;
ThreadPool* Kernel::pool;

__attribute__((noreturn))
static void failure_exit() {
    throw Expt::IRfailureExit("valgrind error exit");
}

static void _vex_log_bytes(const HChar* bytes, SizeT nbytes) {
    std::cout << bytes;
}


unsigned char* _n_page_mem(void* pap) {
    if (((Kernel*)((Pap*)(pap))->state)->is_mode_64()) {
        return ((State<Addr64>*)(((Pap*)(pap))->state))->mem.get_next_page(((Pap*)(pap))->guest_addr);
    }
    else {
        return ((State<Addr32>*)(((Pap*)(pap))->state))->mem.get_next_page(((Pap*)(pap))->guest_addr);
    };
    
}



std::string Expt::ExceptionBase::msg()const {
    switch (m_errorId) {
    case Expt::GuestMem_read_err:return ((Expt::GuestMemReadErr*)(this))->msg();
    case Expt::GuestMem_write_err:return ((Expt::GuestMemWriteErr*)(this))->msg();
    case Expt::IR_failure_exit:return ((Expt::IRfailureExit*)(this))->msg();
    case Expt::Solver_no_solution:return ((Expt::SolverNoSolution*)(this))->msg();
    default:
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
    if (!vex_initdone) {
        Func_Map_Init();
        LibVEX_Init(&failure_exit, &_vex_log_bytes, 0/*debuglevel*/, &vc);

        //for (int i = 0; i < 257; i++) fastalignD1[i] = (((((i)-1) & -8) + 8) >> 3) - 1;
        //for (int i = 0; i < 257; i++) fastalign[i] = (((((i)-1) & -8) + 8) >> 3);
        //for (int i = 0; i <= 64; i++) fastMask[i] = (1ull << i) - 1; fastMask[64] = -1ULL;
        //for (int i = 0; i <= 64; i++) fastMaskI1[i] = (1ull << (i + 1)) - 1; fastMaskI1[63] = -1ULL; fastMaskI1[64] = -1ULL;
        //for (int i = 0; i <= 7; i++) fastMaskB[i] = (1ull << (i << 3)) - 1; fastMaskB[8] = -1ULL;
        //for (int i = 0; i <= 7; i++) fastMaskBI1[i] = (1ull << ((i + 1) << 3)) - 1; fastMaskBI1[7] = -1ULL;
        //for (int i = 0; i <= 64; i++) fastMaskReverse[i] = ~fastMask[i];
        //for (int i = 0; i <= 64; i++) fastMaskReverseI1[i] = ~fastMaskI1[i];

        __m256i m32 = _mm256_setr_epi64x(0x0807060504030201, 0x100f0e0d0c0b0a09, 0x1817161514131211, 0x201f1e1d1c1b1a19);
        for (int i = 0; i <= 32; i++) {
            m32_fast[i] = m32;
            for (int j = i; j <= 32; j++) {
                m32_fast[i].m256i_i8[j] = 0;
            }
            m32_mask_reverse[i] = _mm256_setzero_si256();
            memset(&m32_mask_reverse[i].m256i_i8[i], -1ul, 32 - i);
        }
    }
}


int eval_all(std::vector<Vns>& result, solver& solv, Z3_ast nia) {
    //std::cout << nia << std::endl;
    //std::cout << state.solv.assertions() << std::endl;
    result.reserve(20);
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
            result.emplace_back(Vns(ctx, r));
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
#if defined(OPSTR)
            for (auto s : result) std::cout << ", " << Z3_ast_to_string(ctx, s);
#endif
            solv.pop();
            //for (auto m : mv) Z3_model_dec_ref(ctx, m);
            return result.size();
        }
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
template <typename ADDR> State<ADDR>::State(const char* filename, ADDR gse, Bool _need_record) :
    Kernel((void*)this),
    solv(m_ctx),
    mem(solv, m_ctx, need_record),
    regs(m_ctx, need_record), 
    need_record(_need_record),
    m_status(NewState),
    m_delta(0),
    m_z3_bv_const_n(0),
    m_InvokStack(),
    branch(*this)
{
    vex_info_init(filename);
    if (pool) 
        delete pool;
    pool = new ThreadPool(MaxThreadsNum);


    VexControl vc;
    LibVEX_default_VexControl(&vc);
    vc.iropt_verbosity = 0;
    vc.iropt_level = iropt_level;
    vc.iropt_unroll_thresh = 0;
    vc.guest_max_insns = guest_max_insns;
    vc.guest_chase_thresh = 0;   //不许追赶
    vc.iropt_register_updates_default = iropt_register_updates_default;
    IR_init(vc);
    
    read_mem_dump(MemoryDumpPath);
    if (gse)
        guest_start_ep = gse;
    else {
        guest_start_ep = regs.Iex_Get(gRegsIpOffset(), Ity_I64);
    }
    guest_start = guest_start_ep;


    auto _TraceIrAddrress = doc_debug->FirstChildElement("TraceIrAddrress");
    if (_TraceIrAddrress) {
        for (auto ta = _TraceIrAddrress->FirstChildElement(); ta; ta = ta->NextSiblingElement()) {
            ULong addr; TRControlFlags flag;
            sscanf(ta->Attribute("addr"), "%llx", &addr);
            sscanf(ta->Attribute("cflag"), "%llx", &flag);
            hook_add(addr, nullptr, flag);
        }
    }

};


template <typename ADDR> State<ADDR>::State(State<ADDR>*father_state, ADDR gse) :
    Kernel(*father_state, (void*)this),
    mem(solv, m_ctx, father_state->mem, father_state->need_record),
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


template <typename ADDR> State<ADDR>::operator std::string() const{
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
bool State<ADDR>::get_hook(Hook_struct& hs, ADDR addr)
{
    auto _where = CallBackDict.lower_bound((ADDR)guest_start);
    if (_where == CallBackDict.end()) {
        return false;
    }
    hs = _where->second;
    return true;
}

template <typename ADDR>
Vns State<ADDR>::mk_int_const(UShort nbit) {
    std::unique_lock<std::mutex> lock(m_state_lock);
    auto res = m_z3_bv_const_n++;
    char buff[20];
    sprintf_s(buff, sizeof(buff), "p_%d", res);
    return Vns(m_ctx.bv_const(buff, nbit), nbit);
}

template <typename ADDR>
Vns State<ADDR>::mk_int_const(UShort n, UShort nbit) {
    char buff[20];
    sprintf_s(buff, sizeof(buff), "p_%d", n);
    return  Vns(m_ctx.bv_const(buff, nbit), nbit);
}

template <typename ADDR>
UInt State<ADDR>::getStr(std::stringstream& st, ADDR addr)
{
    UInt p = 0;
    while (True) {
        Vns b = mem.Iex_Load<Ity_I8>(addr++);
        if (b.real()) {
            p++;
            st << (UChar)b;
            if(!(UChar)b) return -1;
        }
        else {
            return p;
        }
    }
    return -1;
}

template <typename ADDR>
void State<ADDR>::hook_del(ADDR addr, TRtype::Hook_CB func)
{
    if (CallBackDict.find(addr) == CallBackDict.end()) {
    }
    else {
        pool->wait();
        auto P = mem.getMemPage(addr);
        if (!P) {
            vex_printf("hook_del: mem access error %p not mapped", addr);
        }
        else {
            P->unit->m_bytes[addr & 0xfff] = CallBackDict[addr].original;
            CallBackDict.erase(CallBackDict.find(addr));
        }
    }
}

template <typename ADDR>
inline IRSB* State<ADDR>::BB2IR() {
    mem.set_double_page(guest_start, pap);
    pap.start_swap       = 0;
    vta_chunk.guest_bytes      = (UChar *)(pap.t_page_addr);
    vta_chunk.guest_bytes_addr = (Addr64)((ADDR)guest_start);
    IRSB *irsb;
    VexRegisterUpdates pxControl;
    VexTranslateResult res;
    if(0){
        TESTCODE(
            irsb = LibVEX_FrontEnd(&vta_chunk, &res, &pxControl, &pap);
        );
    }
    else {
        return LibVEX_FrontEnd(&vta_chunk, &res, &pxControl, &pap);
    }
    return irsb;
}


void TRsolver::add_assert(Vns const& t_assert, Bool ToF)
{
    if ((Z3_context)t_assert != (Z3_context)(*this)) {
        add_assert(t_assert.translate(*this), ToF);
        return;
    }
    if(t_assert.is_bool()){
        if (ToF) {
            Z3_solver_assert(*this, *this, t_assert);
            if (!is_snapshot()) {
                m_asserts.push_back(t_assert);
            }
        }
        else {
            auto not = !t_assert;
            Z3_solver_assert(*this, *this, not);
            if (!is_snapshot()) {
                m_asserts.push_back(not);
            }
        }
    }
    else {
        auto ass = t_assert == Vns(operator Z3_context(), (ULong)ToF, t_assert.bitn);
        Z3_solver_assert(*this, *this, ass);
        if (!is_snapshot()) {
            m_asserts.push_back(ass);
        }
    }
}

inline void TRsolver::add_assert_eq(Vns const& eqA, Vns const& eqB)
{
    if ((Z3_context)eqA != (Z3_context)(*this)) {
        add_assert_eq(eqA.translate(*this), eqB); return;
    }
    if ((Z3_context)eqB != (Z3_context)(*this)) {
        add_assert_eq(eqA, eqB.translate(*this)); return;
    }
    Vns ass = (eqA == eqB);
    Z3_solver_assert(*this, *this, ass);
    if (!is_snapshot()) {
        m_asserts.push_back(ass);
    }
}


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
if (arg0.symbolic()) {\
    z3_mode = True;\
    if (!cptr) { return dirty_call(cee, exp_args, ty); };\
}

template<>
Vns State<Addr32>::CCall(IRCallee *cee, IRExpr **exp_args, IRType ty)
{
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return Vns(m_ctx, ((Function_32_0)(cee->addr))(), bitn);
    void* cptr = funcDict(cee->addr);
    Vns arg0 = tIRExpr(exp_args[0]); CDFCHECK(arg0);
    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(cptr))(arg0) : Vns(m_ctx, ((Function_32_1)(cee->addr))(arg0), bitn);
    Vns arg1 = tIRExpr(exp_args[1]); CDFCHECK(arg1);
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(cptr))(arg0, arg1) : Vns(m_ctx, ((Function_32_2)(cee->addr))(arg0, arg1), bitn);
    Vns arg2 = tIRExpr(exp_args[2]); CDFCHECK(arg2);
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(cptr))(arg0, arg1, arg2) : Vns(m_ctx, ((Function_32_3)(cee->addr))(arg0, arg1, arg2), bitn);
    Vns arg3 = tIRExpr(exp_args[3]); CDFCHECK(arg3);
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(cptr))(arg0, arg1, arg2, arg3) : Vns(m_ctx, ((Function_32_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    Vns arg4 = tIRExpr(exp_args[4]); CDFCHECK(arg4);
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4) : Vns(m_ctx, ((Function_32_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    Vns arg5 = tIRExpr(exp_args[5]); CDFCHECK(arg5);
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5) : Vns(m_ctx, ((Function_32_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
    VPANIC("not support");
}



template<>
Vns State<Addr64>::CCall(IRCallee* cee, IRExpr** exp_args, IRType ty)
{
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return Vns(m_ctx, ((Function_64_0)(cee->addr))(), bitn);

    void* cptr = funcDict(cee->addr);
    Vns arg0 = tIRExpr(exp_args[0]); CDFCHECK(arg0);
    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(cptr))(arg0) : Vns(m_ctx, ((Function_64_1)(cee->addr))(arg0), bitn);
    Vns arg1 = tIRExpr(exp_args[1]); CDFCHECK(arg1);
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(cptr))(arg0, arg1) : Vns(m_ctx, ((Function_64_2)(cee->addr))(arg0, arg1), bitn);
    Vns arg2 = tIRExpr(exp_args[2]); CDFCHECK(arg2);
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(cptr))(arg0, arg1, arg2) : Vns(m_ctx, ((Function_64_3)(cee->addr))(arg0, arg1, arg2), bitn);
    Vns arg3 = tIRExpr(exp_args[3]); CDFCHECK(arg3);
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(cptr))(arg0, arg1, arg2, arg3) : Vns(m_ctx, ((Function_64_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    Vns arg4 = tIRExpr(exp_args[4]); CDFCHECK(arg4);
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4) : Vns(m_ctx, ((Function_64_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    Vns arg5 = tIRExpr(exp_args[5]); CDFCHECK(arg5);
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5) : Vns(m_ctx, ((Function_64_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
    VPANIC("not support");
}
#undef CDFCHECK

template <typename ADDR>
void State<ADDR>::init_irTemp()
{
    for (int j = 0; j < MAX_IRTEMP; j++) {
        ir_temp[j].Vns::Vns(m_ctx, 0);
        //ir_temp[j].m_kind = REAL;
    }
}

template <typename ADDR>
void State<ADDR>::clear_irTemp()
{
    for (int j = 0; j < MAX_IRTEMP; j++) {
        ir_temp[j].~Vns();
    }
}

template <typename ADDR>
void State<ADDR>::read_mem_dump(const char  *filename)
{
    struct memdump {
        unsigned long long nameoffset;
        unsigned long long address;
        unsigned long long length;
        unsigned long long dataoffset;
    }buf;
    FILE *infile;
    infile = fopen(filename, "rb");
    if (!infile) {
        printf("%s, %s", filename, "not exit/n");
        getchar();
        exit(1);
    }
    unsigned long long length, fp, err, name_start_offset, name_end_offset, need_write_size = 0, write_count = 0;
    fread(&length, 8, 1, infile);
    fseek(infile, 24, SEEK_SET);
    name_start_offset = length;
    fread(&name_end_offset, 8, 1, infile);
    length /= 32;
    char *name_buff = (char *)malloc(name_end_offset-name_start_offset);
    fseek(infile, name_start_offset, SEEK_SET);
    fread(name_buff, 1, name_end_offset - name_start_offset, infile);
    fseek(infile, 0, SEEK_SET);
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
        fread(&buf, 32, 1, infile);
        unsigned char *data = (unsigned char *)malloc(buf.length);
        fp = ftell(infile);
        fseek(infile, buf.dataoffset, SEEK_SET);
        fread(data, buf.length, 1, infile);
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
            write_count += mem.write_bytes(buf.address, buf.length, data);
        }
        fseek(infile, fp, SEEK_SET);
        free(data);
    }
    printf("\\-------------------------------------------------------------------------------------/\n");
    QueryPerformanceCounter(&closePerformanceCount);
    printf(
        "Spend time in:   %16lf s.\n"
        "Need to write    %16lf MByte.\n"
        "Actually written %16lf MByte\n", (double)(closePerformanceCount.QuadPart - beginPerformanceCount.QuadPart) / freq.QuadPart, ((double)need_write_size) / 0x100000,((double)write_count)/0x100000);
    free(name_buff);
    fclose(infile);
}

template <typename ADDR>
inline Vns State<ADDR>::ILGop(IRLoadG *lg) {
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
inline Vns State<ADDR>::tIRExpr(IRExpr* e)
{
    switch (e->tag) {
    case Iex_Get: { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
    case Iex_RdTmp: { return ir_temp[e->Iex.RdTmp.tmp]; }
    case Iex_Unop: { return T_Unop(m_ctx, e->Iex.Unop.op, tIRExpr(e->Iex.Unop.arg)); }
    case Iex_Binop: { return T_Binop(m_ctx, e->Iex.Binop.op, tIRExpr(e->Iex.Binop.arg1), tIRExpr(e->Iex.Binop.arg2)); }
    case Iex_Triop: { return T_Triop(m_ctx, e->Iex.Triop.details->op, tIRExpr(e->Iex.Triop.details->arg1), tIRExpr(e->Iex.Triop.details->arg2), tIRExpr(e->Iex.Triop.details->arg3)); }
    case Iex_Qop: { return T_Qop(m_ctx, e->Iex.Qop.details->op, tIRExpr(e->Iex.Qop.details->arg1), tIRExpr(e->Iex.Qop.details->arg2), tIRExpr(e->Iex.Qop.details->arg3), tIRExpr(e->Iex.Qop.details->arg4)); }
    case Iex_Load: { return mem.Iex_Load(tIRExpr(e->Iex.Load.addr), e->Iex.Get.ty); }
    case Iex_Const: { return Vns(m_ctx, e->Iex.Const.con); }
    case Iex_ITE: {
        Vns cond = tIRExpr(e->Iex.ITE.cond);
        return (cond.real()) ?
            ((UChar)cond & 0b1) ? tIRExpr(e->Iex.ITE.iftrue) : tIRExpr(e->Iex.ITE.iffalse)
            :
            Vns(m_ctx, Z3_mk_ite(m_ctx, cond.toZ3Bool(), tIRExpr(e->Iex.ITE.iftrue), tIRExpr(e->Iex.ITE.iffalse)));
    }
    case Iex_CCall: { return CCall(e->Iex.CCall.cee, e->Iex.CCall.args, e->Iex.CCall.retty); }
    case Iex_GetI: {
        auto ix = tIRExpr(e->Iex.GetI.ix);   /*  [e->Iex.GetI.ix, e->Iex.GetI.bias];  */
        assert(ix.real());
        return regs.Iex_Get(e->Iex.GetI.descr->base + (((UInt)(e->Iex.GetI.bias + (int)(ix))) % e->Iex.GetI.descr->nElems)*ty2length(e->Iex.GetI.descr->elemTy), e->Iex.GetI.descr->elemTy);
    };
    case Iex_GSPTR: {
        if (!m_dirty_vex_mode) {
            m_dirty_vex_mode = true;
            m_dctx = dirty_context(this);
        }
        return Vns(m_ctx, dirty_get_gsptr<ADDR>(m_dctx));
    };
    case Iex_VECRET:
    case Iex_Binder:
    default:
        vex_printf("tIRExpr error:  %d", e->tag);
        VPANIC("not support");
    }
}

template <typename ADDR>
bool State<ADDR>::vex_start(Bool first_bkp_pass) {
    Hook_struct hs;
    IRSB* irsb = nullptr;
    if (first_bkp_pass)
        if ((UChar)mem.Iex_Load<Ity_I8>(guest_start) == 0xCC) {
            if (get_hook(hs, guest_start)) {
                goto bkp_pass;
            }
            else {
                if (get_hook(hs, guest_start)) { goto deal_bkp; }
                m_status = Death;
                vex_printf("Ijk_SigTRAP: %p", guest_start);
                goto EXIT;
            }
        }
    State<ADDR>* newBranch = nullptr;
    for (;;) {
    For_Begin:
        irsb = BB2IR();
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
                __m256i m32 = mem.Iex_Load<Ity_V256>(guest_start);
                m32.m256i_i8[0] = hs.original;
                pap.start_swap = 2;
                vta_chunk.guest_bytes = (UChar*)(&m32);
                vta_chunk.guest_bytes_addr = (Addr64)((ADDR)guest_start);
                auto max_insns = pap.guest_max_insns;
                pap.guest_max_insns = 1;
                VexRegisterUpdates pxControl;
                VexTranslateResult res;
                irsb = LibVEX_FrontEnd(&vta_chunk, &res, &pxControl, &pap);
                //ppIRSB(irsb);
                pap.guest_max_insns = max_insns;
            }
        }
    For_Begin_NO_Trans:
        guest_start_of_block = guest_start;
        IRStmt* s = irsb->stmts[0];
        for (UInt stmtn = 0; stmtn < irsb->stmts_used;
            traceIRStmtEnd(s),
            s = irsb->stmts[++stmtn])
        {
            switch (s->tag) {
            case Ist_Put: { regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
            case Ist_Store: { mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; };
            case Ist_WrTmp: { ir_temp[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data); break; };
            case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
                std::unique_lock<std::mutex> lock(m_state_lock);
                IRCAS cas = *(s->Ist.CAS.details);
                Vns addr = tIRExpr(cas.addr);//r10.value
                Vns expdLo = tIRExpr(cas.expdLo);
                Vns dataLo = tIRExpr(cas.dataLo);
                if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
                    Vns expdHi = tIRExpr(cas.expdHi);
                    Vns dataHi = tIRExpr(cas.dataHi);
                    ir_temp[cas.oldHi] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                    ir_temp[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                    mem.Ist_Store(addr, dataLo);
                    mem.Ist_Store(addr + (dataLo.bitn >> 3), dataHi);
                }
                else {//single
                    ir_temp[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                    mem.Ist_Store(addr, dataLo);
                }
                break;
            }
            case Ist_Exit: {
                Vns guard = tIRExpr(s->Ist.Exit.guard).simplify();
                std::vector<Vns> guard_result;
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
                    UInt eval_size = eval_all(guard_result, solv, guard);
                    vassert(eval_size <= 2);
                    if (eval_size == 0) { m_status = Death; goto EXIT; }
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
                    }
                }
                break;
            }
            case Ist_NoOp: break;
            case Ist_IMark: {
                if (m_status == Fork) {
                    State<ADDR>* prv = newBranch;
                    newBranch = (State<ADDR>*)mkState((ADDR)s->Ist.IMark.addr);
                    newBranch->solv.add_assert(prv->solv.get_asserts()[0], False);
                    goto EXIT;
                }
                guest_start = (ADDR)s->Ist.IMark.addr;
                if (is_dynamic_block) {
                    is_dynamic_block = false;
                    goto For_Begin;// fresh changed block
                }
                break;
            };
            case Ist_AbiHint: { //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
                m_InvokStack.push(tIRExpr(s->Ist.AbiHint.nia), tIRExpr(s->Ist.AbiHint.base));
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
                getDirtyVexCtx();
                traceIRStmtEnd(s);
                IRDirty* dirty = s->Ist.Dirty.details;
                Vns guard = tIRExpr(dirty->guard);
                if (guard.symbolic()) {
                    VPANIC("auto guard = m_state.tIRExpr(dirty->guard); symbolic");
                }
                if (((UChar)guard) & 1) {
                    dirty_run<ADDR>(m_dctx, dirty);
                    if (dirty->tmp != IRTemp_INVALID) {
                        ir_temp[dirty->tmp] = dirty_result<ADDR>(m_dctx, typeOfIRTemp(irsb->tyenv, dirty->tmp));
                    }
                }
                break;// fresh changed block
            }
            case Ist_LoadG: {
                IRLoadG* lg = s->Ist.LoadG.details;
                auto guard = tIRExpr(lg->guard);
                if (guard.real()) {
                    ir_temp[lg->dst] = (((UChar)guard)) ? ILGop(lg) : tIRExpr(lg->alt);
                }
                else {
                    ir_temp[lg->dst] = ite(guard == 1, ILGop(lg), tIRExpr(lg->alt));
                }
                break;
            }
            case Ist_StoreG: {
                IRStoreG* sg = s->Ist.StoreG.details;
                auto guard = tIRExpr(sg->guard);
                if (guard.real()) {
                    if ((UChar)guard)
                        mem.Ist_Store(tIRExpr(sg->addr), tIRExpr(sg->data));
                }
                else {
                    auto addr = tIRExpr(sg->addr);
                    auto data = tIRExpr(sg->data);
                    mem.Ist_Store(addr, ite(guard == 1, mem.Iex_Load(addr, (IRType)(data.bitn)), data));
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
            m_InvokStack.pop();
            break;
        }
        case Ijk_Boring: break;
        case Ijk_Call: break;
        case Ijk_SigTRAP: {
        SigTRAP:
            if (get_hook(hs, guest_start)) { goto deal_bkp; }
            m_status = Death;
            vex_printf("Ijk_SigTRAP: %p", guest_start);
            goto EXIT;
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
        Vns next = tIRExpr(irsb->next);
        if (m_status == Fork) {

            State<ADDR>* prv = newBranch;
            Vns& guard = prv->solv.get_asserts()[0];
            if (next.real()) {
                newBranch = (State<ADDR>*)mkState((ADDR)next);
                newBranch->solv.add_assert(guard, False);
            }
            else {
                std::vector<Vns> result;
                UInt eval_size = eval_all(result, solv, next);
                if (eval_size == 0) { m_status = Death; goto EXIT; }
                else if (eval_size == 1) { guest_start = result[0].simplify(); }
                else {
                    for (auto re : result) {
                        ADDR GN = re.simplify();//guest next ip
                        newBranch = (State<ADDR>*)mkState((ADDR)GN);
                        newBranch->solv.add_assert(guard, False);
                        newBranch->solv.add_assert_eq(next, re);
                    }
                }
            }
            goto EXIT;
        }

        if (next.real()) {
            guest_start = next;
        }
        else {
            std::vector<Vns> result;
            UInt eval_size = eval_all(result, solv, next);
            if (eval_size == 0) { m_status = Death; goto EXIT; }
            else if (eval_size == 1) { guest_start = result[0].simplify(); }
            else {
                for (auto re : result) {
                    ADDR GN = re.simplify();//guest next ip
                    newBranch = (State<ADDR>*)mkState((ADDR)GN);
                    newBranch->solv.add_assert_eq(next, re);
                }
                m_status = Fork;
                goto EXIT;
            }
        }
    };

EXIT:

}

template <typename ADDR>
void State<ADDR>::start(Bool first_bkp_pass) {
    pap.state = (void*)(this);
    pap.n_page_mem = _n_page_mem;
    pap.guest_max_insns = guest_max_insns;
    init_vta_chunk(vta_chunk, vge_chunk, guest, traceflags);

    vassert(this->m_status == NewState);
    m_status = Running;
    traceStart();
    is_dynamic_block = false;
    init_irTemp();


Begin_try:
    try {
        vex_start(first_bkp_pass);
    }
    catch (Expt::ExceptionBase & error) {
        switch ((Expt::ExceptionTag)error) {
        case Expt::GuestMem_read_err:
        case Expt::GuestMem_write_err: {
            try {
                cpu_exception();
            }
            catch (Expt::ExceptionBase & cpu_exception_error) {
                std::cout << "Usage issues or simulation software problems.\nError message:" << std::endl;
                std::cout << error << std::endl;
                m_status = Death;
            }
            break;
        }
        case Expt::IR_failure_exit: {
            std::cout << "Sorry This could be my design error. (BUG)\nError message:" << std::endl;
            std::cout << error << std::endl;
            exit(1);
        }
        case Expt::Solver_no_solution: {
            std::cout << " There is no solution to this problem. But this COULD BE my design error (BUG).\nError message:" << std::endl;
            std::cout << error << std::endl;
            exit(1);
        }
        };
    }

    if (m_status == Exception) {
        m_status = Running;
        goto Begin_try;
    }

    traceFinish(); 
    clear_irTemp();
    return;
}


template <typename ADDR>
void State <ADDR>::branchGo()
{
    for(auto b : branch){
        State::pool->enqueue([b] {
            b->start(True);
            });
    }
}

template<typename ADDR>
class StateCmprsInterface {
    cmpr::StateType m_type;
    cmpr::CmprsContext<State<ADDR>, State_Tag>& m_ctx;
    State<ADDR>& m_state;
    Vns m_condition;
    static bool StateCompression(State<ADDR>& a, State<ADDR> const& next) {
        bool ret = a.m_InvokStack == next.m_InvokStack;// 压缩条件
        return ret && a.StateCompression(next);//支持扩展条件
    }

    static void StateCompressMkSymbol(State<ADDR>& a, State<ADDR> const& newState) {
        a.m_InvokStack = newState.m_InvokStack;// 使其满足压缩条件
        a.StateCompressMkSymbol(newState);//支持
    }

    std::vector<Vns>& get_asserts() const { return m_state.solv.get_asserts(); };

public:
    StateCmprsInterface(
        cmpr::CmprsContext<State<ADDR>, State_Tag>& ctx,
        State<ADDR>& self,
        cmpr::StateType type
    ) :
        m_ctx(ctx), m_state(self), m_type(type), m_condition(ctx, 0, 0)
    { };

    cmpr::CmprsContext<State<ADDR>, State_Tag>& cctx() { return m_ctx; }
    cmpr::StateType type() { return m_type; };

    Vns const& get_assert() {
        if (!m_condition.bitn) {
            m_condition = cmpr::logic_and(get_asserts()).translate(m_ctx.ctx());
        }
        return m_condition;
    }

    void get_write_map(std::hash_map<Addr64, bool>& record) {
        if (m_state.regs.record) {
            for (auto offset : *m_state.regs.record) {
                record[offset];
            }
        }
        for (auto mcm : m_state.mem.change_map()) {
            vassert(mcm.second->record != NULL);
            for (auto offset : *(mcm.second->record)) {
                auto Address = mcm.first + offset;
                auto p = m_state.mem.getMemPage(Address);
                vassert(p);
                vassert(p->user == m_state.mem.get_user());
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

    Vns mem_Load(ADDR addr) {
        return m_state.mem.Iex_Load<Ity_I64>(addr).translate(m_ctx.ctx());
    }

    Vns reg_Get(UInt offset) {
        return m_state.regs.Iex_Get<Ity_I64>(offset).translate(m_ctx.ctx());
    }

    Vns read(ADDR addr) {
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

#define PPCMPR

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
            Vns condition = state.conditions().translate(*nbranch);
#ifdef  PPCMPR
            printf("%s\n", Z3_ast_to_string(condition, condition));
#endif //  _DEBUG
            nbranch->solv.add_assert(condition);
            std::hash_map<Addr64, cmpr::GPMana> const& cm = state.changes();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator itor = cm.begin();
            std::hash_map<Addr64, cmpr::GPMana>::const_iterator end = cm.end();

            for (; itor != end; itor++) {
                Addr64 addr = itor->first;
                Vns value = itor->second.get().translate(*nbranch);
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
            Vns condition = state.conditions();
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
                Vns value = itor->second.get();
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


template State<Addr32>::State(State<Addr32>* father_state, Addr32 gse);
template State<Addr64>::State(State<Addr64>* father_state, Addr64 gse);
template State<Addr32>::State(const char* filename, Addr32 gse, Bool _need_record);
template State<Addr64>::State(const char* filename, Addr64 gse, Bool _need_record);
template Vns State<Addr32>::mk_int_const(UShort nbit);
template Vns State<Addr64>::mk_int_const(UShort nbit);
template UInt State<Addr32>::getStr(std::stringstream& st, Addr32 addr);
template UInt State<Addr64>::getStr(std::stringstream& st, Addr64 addr);
template State<Addr32>::~State();
template State<Addr64>::~State();
template void State<Addr32>::compress(cmpr::CmprsContext<State<Addr32>, State_Tag>&);
template void State<Addr64>::compress(cmpr::CmprsContext<State<Addr64>, State_Tag>&);
template State<Addr32>::operator std::string() const;
template State<Addr64>::operator std::string() const;
template void State<Addr32>::start(Bool first_bkp_pass);
template void State<Addr64>::start(Bool first_bkp_pass);
