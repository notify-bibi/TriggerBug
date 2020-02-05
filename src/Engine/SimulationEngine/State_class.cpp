
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
    throw (z3::exception("failure_exit exception  "));
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
    mem(*this, m_ctx,need_record),
    regs(m_ctx, need_record), 
    need_record(_need_record),
    status(NewState),
    m_delta(0),
    m_z3_bv_const_n(0),
    m_father_state(nullptr),
    m_InvokStack()
{
    vex_info_init(filename);
    if (pool) 
        delete pool;
    pool = new ThreadPool(MaxThreadsNum);

    branch.reserve(5);

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
    mem(*this, father_state->mem, m_ctx, father_state->need_record),
    guest_start_ep(gse),
    guest_start(guest_start_ep), 
    solv(m_ctx, father_state->solv,  z3::solver::translate{}),
    regs(father_state->regs, m_ctx, father_state->need_record),
    need_record(father_state->need_record),
    status(NewState),
    m_delta(0),
    m_z3_bv_const_n(father_state->m_z3_bv_const_n),
    m_father_state(father_state),
    m_InvokStack(father_state->m_InvokStack)
{

};



template <typename ADDR> State<ADDR>::~State() {
    if (branch.size()) {
        for (auto s : branch) {
            delete s;
        }
    }
    if (m_dirty_vex_mode) {
        dirty_context_del<ADDR>(m_dctx);
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

    switch (status) {
    case NewState:str.append("NewState "); break;
    case Running:str.append("Running "); break;
    case Fork:str.append("Fork "); break;
    case Death:str.append("Death "); break;
    default:
        snprintf(hex, sizeof(hex),  "%d ", status);
        strContent.assign(hex);
        str.append(strContent); break;
    }

    str.append(" #child{\n");
    if (branch.empty()) {
        switch (status) {
        case NewState:str.append("NewState "); break;
        case Running:str.append("Running "); break;
        case Fork:str.append("Fork "); break;
        case Death:str.append("Death "); break;
        default:
            snprintf(hex, sizeof(hex),  "%d ", status);
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

template<>
Vns State<Addr32>::CCall(IRCallee *cee, IRExpr **exp_args, IRType ty)
{
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return Vns(m_ctx, ((Function_32_0)(cee->addr))(), bitn);
    Vns arg0 = tIRExpr(exp_args[0]);
    if (arg0.symbolic()) z3_mode = True;

    void* cptr = funcDict(cee->addr);
    if (!m_dirty_vex_mode) {
        m_dirty_vex_mode = true;
        m_dctx = dirty_context(this);
    }
    if (!cptr) {
        return dirty_ccall<Addr32>(m_dctx, ty, cee, exp_args);
    };

    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(cptr))(arg0) : Vns(m_ctx, ((Function_32_1)(cee->addr))(arg0), bitn);
    Vns arg1 = tIRExpr(exp_args[1]);
    if (arg1.symbolic()) z3_mode = True;
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(cptr))(arg0, arg1) : Vns(m_ctx, ((Function_32_2)(cee->addr))(arg0, arg1), bitn);
    Vns arg2 = tIRExpr(exp_args[2]);
    if (arg2.symbolic()) z3_mode = True;
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(cptr))(arg0, arg1, arg2) : Vns(m_ctx, ((Function_32_3)(cee->addr))(arg0, arg1, arg2), bitn);
    Vns arg3 = tIRExpr(exp_args[3]);
    if (arg3.symbolic()) z3_mode = True;
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(cptr))(arg0, arg1, arg2, arg3) : Vns(m_ctx, ((Function_32_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    Vns arg4 = tIRExpr(exp_args[4]);
    if (arg4.symbolic()) z3_mode = True;
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4) : Vns(m_ctx, ((Function_32_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    Vns arg5 = tIRExpr(exp_args[5]);
    if (arg5.symbolic()) z3_mode = True;
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5) : Vns(m_ctx, ((Function_32_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
}

template<>
Vns State<Addr64>::CCall(IRCallee* cee, IRExpr** exp_args, IRType ty)
{
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return Vns(m_ctx, ((Function_64_0)(cee->addr))(), bitn);
    Vns arg0 = tIRExpr(exp_args[0]);
    if (arg0.symbolic()) z3_mode = True;

    void* cptr = funcDict(cee->addr);
    if (!m_dirty_vex_mode) {
        m_dirty_vex_mode = true;
        m_dctx = dirty_context(this);
    }
    if (!cptr) {
        return dirty_ccall<Addr64>(m_dctx, ty, cee, exp_args);
    };

    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(cptr))(arg0) : Vns(m_ctx, ((Function_64_1)(cee->addr))(arg0), bitn);
    Vns arg1 = tIRExpr(exp_args[1]);
    if (arg1.symbolic()) z3_mode = True;
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(cptr))(arg0, arg1) : Vns(m_ctx, ((Function_64_2)(cee->addr))(arg0, arg1), bitn);
    Vns arg2 = tIRExpr(exp_args[2]);
    if (arg2.symbolic()) z3_mode = True;
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(cptr))(arg0, arg1, arg2) : Vns(m_ctx, ((Function_64_3)(cee->addr))(arg0, arg1, arg2), bitn);
    Vns arg3 = tIRExpr(exp_args[3]);
    if (arg3.symbolic()) z3_mode = True;
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(cptr))(arg0, arg1, arg2, arg3) : Vns(m_ctx, ((Function_64_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    Vns arg4 = tIRExpr(exp_args[4]);
    if (arg4.symbolic()) z3_mode = True;
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(cptr))(arg0, arg1, arg2, arg3, arg4) : Vns(m_ctx, ((Function_64_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    Vns arg5 = tIRExpr(exp_args[5]);
    if (arg5.symbolic()) z3_mode = True;
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(cptr))(arg0, arg1, arg2, arg3, arg4, arg5) : Vns(m_ctx, ((Function_64_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);

}

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
void State<ADDR>::start(Bool first_bkp_pass) {
    pap.state = (void*)(this);
    pap.n_page_mem = _n_page_mem;
    pap.guest_max_insns = guest_max_insns;
    init_vta_chunk(vta_chunk, vge_chunk, guest, traceflags);

    if (this->status != NewState) {
        vex_printf("this->status != NewState");
        return;
    }
    IRSB* irsb = nullptr;
    status = Running;
    traceStart();
    g_state = this;
    is_dynamic_block = false;
    Hook_struct hs;
    init_irTemp();
Begin_try:
    try {
        try {
            if(first_bkp_pass)
                if ((UChar)mem.Iex_Load<Ity_I8>(guest_start) == 0xCC) {
                    if (get_hook(hs, guest_start)) {
                        goto bkp_pass;
                    }
                    else {
                        if (get_hook(hs, guest_start)) { goto deal_bkp; }
                        status = Death;
                        vex_printf("Ijk_SigTRAP: %p", guest_start); 
                        goto EXIT;
                    }
                }

            for (;;) {
For_Begin:
                irsb = BB2IR();
                traceIRSB(irsb);
                goto For_Begin_NO_Trans;
            deal_bkp:
                {
                    status = _call_back_hook(hs);
                    if (status != Running) {
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
                            if ((UChar)guard) {
                            Exit_guard_true:
                                if (s->Ist.Exit.jk > Ijk_Ret)
                                {
                                    //ppIRSB(irsb);
                                    status = Ijk_call(s->Ist.Exit.jk);
                                    if (status != Running) {
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
                            }
                        }
                        else {
                            UInt eval_size = eval_all(guard_result, solv, guard);
                            vassert(eval_size <= 2);
                            if (eval_size == 0) { status = Death; goto EXIT; }
                            if (eval_size == 1) {
                                if (((UChar)guard_result[0].simplify()) & 1)
                                    goto Exit_guard_true;
                            }
                            if (eval_size == 2) {
                                if (s->Ist.Exit.jk > Ijk_Ret){
                                    solv.add_assert(guard, False);
                                }
                                else {
                                    branchChunks.emplace_back(BranchChunk(s->Ist.Exit.dst->Ico.U64, Vns(m_ctx, 0), guard, True));
                                    status = Fork;
                                }
                            }
                        }
                        break;
                    }
                    case Ist_NoOp: break;
                    case Ist_IMark: {
                        if (status == Fork) {
                            branchChunks.emplace_back(BranchChunk((ADDR)s->Ist.IMark.addr, Vns(m_ctx, 0), branchChunks[0].m_guard, False));
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
                        if (!m_dirty_vex_mode) {
                            m_dirty_vex_mode = true;
                            m_dctx = dirty_context(this);
                        }
                        traceIRStmtEnd(s);
                        dirty_run<ADDR>(m_dctx,
                            s->Ist.Dirty.details->tmp == IRTemp_INVALID ? nullptr : &(ir_temp[s->Ist.Dirty.details->tmp]),
                            s->Ist.Dirty.details->tmp == IRTemp_INVALID ? Ity_I64 : typeOfIRTemp(irsb->tyenv, s->Ist.Dirty.details->tmp),
                            s->Ist.Dirty.details);
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
                    case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/{
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
                case Ijk_Boring:        break;
                case Ijk_Call: {break; }
                case Ijk_Ret:{
                    m_InvokStack.pop();
                    break;
                }
                case Ijk_SigTRAP: {
                SigTRAP:
                    if (get_hook(hs, guest_start)) { goto deal_bkp; }
                    status = Death;
                    vex_printf("Ijk_SigTRAP: %p", guest_start);
                    goto EXIT;
                }
                default: {
                    status = Ijk_call(irsb->jumpkind);
                    if (status != Running) {
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
                Vns next = tIRExpr(irsb->next).simplify();
                if (status == Fork) {
                    Vns& guard = branchChunks[0].m_guard;
                    if (next.real()) {
                        branchChunks.emplace_back(BranchChunk(next, Vns(m_ctx, 0), guard, False));
                    }
                    else {
                        std::vector<Vns> result;
                        UInt eval_size = eval_all(result, solv, next);
                        if (eval_size == 0) { status = Death; goto EXIT; }
                        else if (eval_size == 1) { guest_start = result[0].simplify(); }
                        else {
                            for (auto re : result) {
                                ADDR GN = re.simplify();//guest next ip
                                branchChunks.emplace_back(BranchChunk(GN, next, guard, False));
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
                    if (eval_size == 0) { status = Death; goto EXIT; }
                    else if (eval_size == 1) { guest_start = result[0].simplify(); }
                    else {
                        for (auto re : result) {
                            ADDR GN = re.simplify();//guest next ip
                            branchChunks.emplace_back(BranchChunk(GN, next, Vns(m_ctx, 0), False));
                        }
                        status = Fork;
                        goto EXIT;
                    }
                }
            };

        }
        catch (TRMem::MEMexception & error) {
            std::cout <<"guest ip: "<< std::hex << guest_start <<" "<< error << std::endl;
            try {
                cpu_exception();
                if (status = Death) {
                    status = Death;
                }
            }catch (TRMem::MEMexception & error) {
                status = Death;
            }
        }
    }
    catch (exception & error) {
        vex_printf("unexpected z3 error: at %llx\n", guest_start);
        std::cout << error << std::endl;
        status = Death;
    }
    
    if (status == Exception) {
        status = Running;
        goto Begin_try;
    }
EXIT:
    traceFinish(); 
    clear_irTemp();
    return;

}


template <typename ADDR>
void State<ADDR>::branchGo()
{
    for(auto b : branch){
        State::pool->enqueue([b] {
            b->start(True);
            });
    }
}

template <typename ADDR>
State<ADDR>* State<ADDR>::mkChildState(BranchChunk const& bc)
{
    State* ns = ForkState(bc.m_oep);
    if (bc.m_guard.symbolic()) {
        ns->solv.add_assert(bc.m_guard.translate(ns->m_ctx), bc.m_tof);
    }
    if (bc.m_sym_addr.symbolic()) {
        ns->solv.add_assert_eq(bc.m_sym_addr.translate(ns->m_ctx), Vns(ns->m_ctx, bc.m_oep));
    }
    return ns;
}

template<typename ADDR, class TC>
inline void StatePrinter<ADDR, TC>::spIRExpr(const IRExpr* e)

{
    Int i;
    switch (e->tag) {
    case Iex_Binder:
        vex_printf("BIND-%d", e->Iex.Binder.binder);
        break;
    case Iex_Get:
        vex_printf("GET:");
        ppIRType(e->Iex.Get.ty);
        vex_printf("(%d)", e->Iex.Get.offset);
        break;
    case Iex_GetI:
        vex_printf("GETI");
        ppIRRegArray(e->Iex.GetI.descr);
        vex_printf("[");
        spIRExpr(e->Iex.GetI.ix);
        vex_printf(",%d]", e->Iex.GetI.bias);
        break;
    case Iex_RdTmp:
        spIRTemp(e->Iex.RdTmp.tmp);
        break;
    case Iex_Qop: {
        const IRQop* qop = e->Iex.Qop.details;
        ppIROp(qop->op);
        vex_printf("(");
        spIRExpr(qop->arg1);
        vex_printf(",");
        spIRExpr(qop->arg2);
        vex_printf(",");
        spIRExpr(qop->arg3);
        vex_printf(",");
        spIRExpr(qop->arg4);
        vex_printf(")");
        break;
    }
    case Iex_Triop: {
        const IRTriop* triop = e->Iex.Triop.details;
        ppIROp(triop->op);
        vex_printf("(");
        spIRExpr(triop->arg1);
        vex_printf(",");
        spIRExpr(triop->arg2);
        vex_printf(",");
        spIRExpr(triop->arg3);
        vex_printf(")");
        break;
    }
    case Iex_Binop:
        ppIROp(e->Iex.Binop.op);
        vex_printf("(");
        spIRExpr(e->Iex.Binop.arg1);
        vex_printf(",");
        spIRExpr(e->Iex.Binop.arg2);
        vex_printf(")");
        break;
    case Iex_Unop:
        ppIROp(e->Iex.Unop.op);
        vex_printf("(");
        spIRExpr(e->Iex.Unop.arg);
        vex_printf(")");
        break;
    case Iex_Load:
        vex_printf("LD%s:", e->Iex.Load.end == Iend_LE ? "le" : "be");
        ppIRType(e->Iex.Load.ty);
        vex_printf("(");
        spIRExpr(e->Iex.Load.addr);
        vex_printf(")");
        break;
    case Iex_Const:
        ppIRConst(e->Iex.Const.con);
        break;
    case Iex_CCall:
        ppIRCallee(e->Iex.CCall.cee);
        vex_printf("(");
        for (i = 0; e->Iex.CCall.args[i] != NULL; i++) {
            IRExpr* arg = e->Iex.CCall.args[i];
            spIRExpr(arg);

            if (e->Iex.CCall.args[i + 1] != NULL) {
                vex_printf(",");
            }
        }
        vex_printf("):");
        ppIRType(e->Iex.CCall.retty);
        break;
    case Iex_ITE:
        vex_printf("ITE(");
        spIRExpr(e->Iex.ITE.cond);
        vex_printf(",");
        spIRExpr(e->Iex.ITE.iftrue);
        vex_printf(",");
        spIRExpr(e->Iex.ITE.iffalse);
        vex_printf(")");
        break;
    case Iex_VECRET:
        vex_printf("VECRET");
        break;
    case Iex_GSPTR:
        vex_printf("GSPTR");
        break;
    default:
        VPANIC("ppIRExpr");
    }
}

template<typename ADDR, class TC>
void StatePrinter<ADDR, TC>::spIRTemp(IRTemp tmp)

{
    if (tmp == IRTemp_INVALID)
        vex_printf("IRTemp_INVALID");
    else
    {
        vex_printf("t%u: ", tmp);
        std::cout << ir_temp[tmp];
    }
}

template<typename ADDR, class TC>
void StatePrinter<ADDR, TC>::spIRPutI(const IRPutI* puti)
{
    vex_printf("PUTI");
    ppIRRegArray(puti->descr);
    vex_printf("[");
    ppIRExpr(puti->ix);
    vex_printf(",%d] = ", puti->bias);
    ppIRExpr(puti->data);
}

template<typename ADDR, class TC>
void StatePrinter<ADDR, TC>::spIRStmt(const IRStmt* s)

{
    if (!s) {
        vex_printf("!!! IRStmt* which is NULL !!!");
        return;
    }
    switch (s->tag) {
    case Ist_NoOp:
        vex_printf("IR-NoOp");
        break;
    case Ist_IMark:
        vex_printf("------ IMark(0x%llx, %u, %u) ------",
            s->Ist.IMark.addr, s->Ist.IMark.len,
            (UInt)s->Ist.IMark.delta);
        break;
    case Ist_AbiHint:
        vex_printf("====== AbiHint(");
        spIRExpr(s->Ist.AbiHint.base);
        vex_printf(", %d, ", s->Ist.AbiHint.len);
        spIRExpr(s->Ist.AbiHint.nia);
        vex_printf(") ======");
        break;
    case Ist_Put:
        vex_printf("PUT(%d) = ", s->Ist.Put.offset);
        spIRExpr(s->Ist.Put.data);
        break;
    case Ist_PutI:
        ppIRPutI(s->Ist.PutI.details);
        break;
    case Ist_WrTmp:
        ppIRTemp(s->Ist.WrTmp.tmp);
        vex_printf(" = ");
        spIRExpr(s->Ist.WrTmp.data);
        break;
    case Ist_Store:
        vex_printf("ST%s(", s->Ist.Store.end == Iend_LE ? "le" : "be");
        spIRExpr(s->Ist.Store.addr);
        vex_printf(") = ");
        spIRExpr(s->Ist.Store.data);
        break;
    case Ist_StoreG:
        ppIRStoreG(s->Ist.StoreG.details);
        break;
    case Ist_LoadG:
        ppIRLoadG(s->Ist.LoadG.details);
        break;
    case Ist_CAS:
        ppIRCAS(s->Ist.CAS.details);
        break;
    case Ist_LLSC:
        if (s->Ist.LLSC.storedata == NULL) {
            spIRTemp(s->Ist.LLSC.result);
            vex_printf(" = LD%s-Linked(",
                s->Ist.LLSC.end == Iend_LE ? "le" : "be");
            spIRExpr(s->Ist.LLSC.addr);
            vex_printf(")");
        }
        else {
            spIRTemp(s->Ist.LLSC.result);
            vex_printf(" = ( ST%s-Cond(",
                s->Ist.LLSC.end == Iend_LE ? "le" : "be");
            spIRExpr(s->Ist.LLSC.addr);
            vex_printf(") = ");
            spIRExpr(s->Ist.LLSC.storedata);
            vex_printf(" )");
        }
        break;
    case Ist_Dirty:
        ppIRDirty(s->Ist.Dirty.details);
        break;
    case Ist_MBE:
        vex_printf("IR-");
        ppIRMBusEvent(s->Ist.MBE.event);
        break;
    case Ist_Exit:
        vex_printf("if (");
        spIRExpr(s->Ist.Exit.guard);
        vex_printf(") { PUT(%d) = ", s->Ist.Exit.offsIP);
        ppIRConst(s->Ist.Exit.dst);
        vex_printf("; exit-");
        ppIRJumpKind(s->Ist.Exit.jk);
        vex_printf(" } ");
        break;
    default:
        VPANIC("ppIRStmt");
    }
}

static inline bool is_avoid(std::vector<State_Tag>& avoid, State_Tag tag) { return (find(avoid.begin(), avoid.end(), tag) != avoid.end()); }

template <typename ADDR>
void State<ADDR>::get_write_map(
    std::hash_map<ADDR, Vns>& change_map_ret, TRcontext& ctx
) {
    UInt size = regs.record->get_count();
    for (auto mcm : mem.mem_change_map) {
        size += mcm.second->record->get_count();
    }
    change_map_ret.reserve(size);
    if (regs.record) {
        for (auto offset : *regs.record) {
            change_map_ret[offset] = regs.Iex_Get<Ity_I64>(offset, ctx);
        }
    }
    for (auto mcm : mem.mem_change_map) {
        vassert(mcm.second->record != NULL);
        for (auto offset : *(mcm.second->record)) {
            auto Address = mcm.first + offset;
            auto p = mem.getMemPage(Address);
            vassert(p);
            vassert(p->user == mem.user);
            vassert(Address > REGISTER_LEN);
            change_map_ret[Address] = p->unit->Iex_Get<Ity_I64>(offset, ctx);
        }
    }
    vassert(size == change_map_ret.size());
}

template <typename ADDR>
static UInt divide_into_groups(std::vector<State<ADDR>*>& group, State<ADDR>* s) {
    UInt group_count = 0;
    for (auto gs : group) {
        if (gs->_StateCompression(*s)) {
            return group_count;
        }
        group_count++;
    }
    group.emplace_back(s);
    return group_count;
}

template <typename ADDR>
StateCompressNode<ADDR>* State<ADDR>::mkCompressTree(
    std::vector<State*>& group, ADDR Target_Addr, State_Tag Target_Tag, std::vector<State_Tag>& avoid
) {
    if (branch.empty()) {
        if (status == Target_Tag) {
            if (guest_start == Target_Addr) {
                StateCompressNode<ADDR>* delnode = new StateCompressNode<ADDR>;
                delnode->state = this;
                delnode->State_flag = 1;
                delnode->compress_group = divide_into_groups(group, this);
                return delnode;
            }
            else {
                return nullptr;
            }
        }
        else {
            if (is_avoid(avoid, status)) {
                StateCompressNode<ADDR>* delnode = new StateCompressNode<ADDR>;
                delnode->state = this;
                delnode->State_flag = 0;
                return delnode;
            }
            else {
                return nullptr;
            }
        }
    }
    else {
        vassert(status == Fork);
        StateCompressNode<ADDR>* delnode = new StateCompressNode<ADDR>;
        delnode->state = this;
        delnode->State_flag = 2;
        std::vector<State<ADDR>*> avoid_assert;
        std::vector<State<ADDR>*>::iterator b_end = branch.end();
        for (auto it = branch.begin(); it != b_end;) {
            State<ADDR>* child_state = *it;
            StateCompressNode<ADDR>* ret_del_node = child_state->mkCompressTree(group, Target_Addr, Target_Tag, avoid);
            if (ret_del_node) {
                delnode->child_nodes.emplace_back(ret_del_node);
            }
            else {
                avoid_assert.emplace_back(child_state);
            }
            it++;
        }
        if (delnode->child_nodes.empty()) {
            delete delnode;
            return nullptr;
        }
        else {
            delnode->avoid_assert_state = avoid_assert;
            return delnode;
        }
    }
}

template <typename ADDR>
bool State<ADDR>::treeCompress(
    Vns& avoid_asserts_ret, bool &has_branch,
    std::hash_map<ADDR, Vns>& change_map_ret,
    StateCompressNode<ADDR>* SCNode, UInt group, TRcontext& ctx, UInt deep
    ) {
    vassert(SCNode->state == this);
    if (SCNode->State_flag == 1) {
        vassert(branch.empty());
        has_branch = false;
        if (SCNode->compress_group == group) {
           SCNode->state->get_write_map(change_map_ret, ctx);
            auto op = SCNode->state->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::CC_OP);
            return true;
        }
        else {
            avoid_asserts_ret = solv.getassert(ctx);
            return false;
        }
    }
    else if (SCNode->State_flag == 0) {
        has_branch = false;
        avoid_asserts_ret = solv.getassert(ctx);
        return false;
    }
    else {
        Vns avoid_asserts(ctx,1,1);
        bool first = true;
        std::hash_map<ADDR, bool> change_address;                   //change_address.reserve(200);
        std::vector <std::hash_map<ADDR, Vns>> change_map_temp;     change_map_temp.reserve(10);
        std::vector <State*> change_map_states;                     change_map_states.reserve(10);
        change_map_temp.emplace_back(std::hash_map<ADDR, Vns>());
        for (auto child_node_it = SCNode->child_nodes.begin(); child_node_it != SCNode->child_nodes.end();) {
            StateCompressNode<ADDR>* child_node = *child_node_it;
            bool child_has_branch = false;
            Vns avoid_asserts_temp(ctx, 1, 1);
            if (child_node->state->treeCompress(avoid_asserts_temp, child_has_branch, change_map_temp.back(), child_node, group, ctx, deep + 1)) {
                for (auto tmp_it : change_map_temp.back()){
                    change_address[tmp_it.first] = true;
                }
                change_map_states.emplace_back(child_node->state);
                change_map_temp.emplace_back(std::hash_map<ADDR, Vns>());
                if (child_has_branch) {
                    has_branch = true;
                }
            }
            else {
                change_map_temp.back().clear();
            }
            if (first&&avoid_asserts_temp.symbolic()) {
                first = false;
                avoid_asserts = avoid_asserts_temp;
            }
            else if(avoid_asserts_temp.symbolic()) {
                avoid_asserts = avoid_asserts || avoid_asserts_temp;
            }
            child_node_it++;
        }
        for (auto cs : SCNode->avoid_assert_state) {
            if (first) {
                first = false;
                avoid_asserts = cs->solv.getassert(ctx);
            }
            else {
                avoid_asserts = avoid_asserts || cs->solv.getassert(ctx);
            }
        }
        if(deep){
            if (avoid_asserts.symbolic()) {
                if (ctx == m_ctx) {
                    avoid_asserts_ret = solv.getassert() && avoid_asserts;
                }
                else {
                    avoid_asserts_ret = solv.getassert(ctx) && avoid_asserts;
                }
            }
        }
        else {
            avoid_asserts_ret = avoid_asserts;
        }
        if (!has_branch) {
            has_branch = SCNode->avoid_assert_state.size() != 0;
        }
        if (change_map_temp.size() == 1) {
            return false;
        }
        else {
            std::vector<std::hash_map<ADDR, Vns>>::iterator cmt_it = change_map_temp.begin();

            std::hash_map<ADDR, Vns> change_map_fork_state;
            if (deep) {
                SCNode->state->get_write_map(change_map_fork_state, ctx);
            }
            change_map_ret.reserve(change_address.size() + change_map_fork_state.size());

            for (UInt idx = 0; idx < change_map_temp.size() - 1; idx++) {
                State* cld_state = change_map_states[idx];
                for (auto ca : change_address) {
                    {
                        auto _Where = (*cmt_it).lower_bound(ca.first);
                        if (_Where == (*cmt_it).end()) {
                            if (ca.first < REGISTER_LEN) {
                                if (ctx == cld_state->m_ctx) {
                                    (*cmt_it)[ca.first] = cld_state->regs.Iex_Get<Ity_I64>(ca.first);
                                }
                                else {
                                    (*cmt_it)[ca.first] = cld_state->regs.Iex_Get<Ity_I64>(ca.first, ctx);
                                }
                            }
                            else {
                                auto p = cld_state->mem.getMemPage(ca.first);
                                if (ctx == p->unit->m_ctx) {
                                    (*cmt_it)[ca.first] = p->unit->Iex_Get<Ity_I64>(ca.first & 0xfff);
                                }else{
                                    (*cmt_it)[ca.first] = p->unit->Iex_Get<Ity_I64>(ca.first & 0xfff, ctx);
                                }
                            }
                        }
                    };
                    {
                        auto _Where = change_map_ret.lower_bound(ca.first);
                        if (_Where == change_map_ret.end()) {
                            change_map_ret[ca.first] = (*cmt_it)[ca.first];
                        }
                        else {
                            if ((((*cmt_it)[ca.first].real()) && (_Where->second.real())) && ((ULong)((*cmt_it)[ca.first]) == (ULong)(_Where->second))) {
                            }
                            else {
                                _Where->second = Vns(ctx, Z3_mk_ite(ctx, cld_state->solv.getassert(ctx), (*cmt_it)[ca.first], _Where->second), 64);
                            }
                        }
                    };
                }
                cmt_it++;
            }
            vassert(change_map_ret.size() == change_address.size());
            if(deep){
                for (auto ca : change_map_fork_state) {
                    auto _Where = change_map_ret.lower_bound(ca.first);
                    if (_Where == change_map_ret.end()) {
                        change_map_ret[ca.first] = ca.second;
                    }
                }
            }
            return true;
        }
    }
}

template <typename ADDR>
static bool delete_avoid_state(StateCompressNode<ADDR>* node) {
    if (node->child_nodes.empty()) {
        return true;
    }
    for (auto child_node = node->child_nodes.begin(); child_node != node->child_nodes.end();) {
        if (delete_avoid_state(*child_node)) {
            auto fd = find(node->state->branch.begin(), node->state->branch.end(), (*child_node)->state);
            if (fd != node->state->branch.end()) {
                node->state->branch.erase(fd);
                delete (*child_node)->state;
                delete *child_node;
                child_node = node->child_nodes.erase(child_node);
                continue;
            }
            else {
                VPANIC("impossible");
            }
        }
        child_node++;
    }
    if (node->state->branch.empty()) {
        return true;
    }
    else {
        delete node;
        return false;
    }
}


template <typename ADDR>
void State<ADDR>::set_changes(std::hash_map<ADDR, Vns>& change_map) {
    for (auto map_it : change_map) {
        if (map_it.first < REGISTER_LEN) {
#ifdef  _DEBUG
            std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
            regs.Ist_Put(map_it.first, map_it.second);

        }
        else {
#ifdef  _DEBUG
            std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
            mem.Ist_Store(map_it.first, map_it.second);
        }
    };
}

template <typename ADDR>
void State<ADDR>::set_changes(std::hash_map<ADDR, Vns>& change_map, z3::solver::translate) {
    for (auto map_it : change_map) {
        if (map_it.first < REGISTER_LEN) {
#ifdef  _DEBUG
            std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
            regs.Ist_Put(map_it.first, map_it.second.translate(m_ctx));

        }
        else {
#ifdef  _DEBUG
            std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
            mem.Ist_Store(map_it.first, map_it.second.translate(m_ctx));
        }
    };
}

template <typename ADDR>
void State<ADDR>::compress(ADDR Target_Addr, State_Tag Target_Tag, std::vector<State_Tag>& avoid)
{
    std::vector<State*> group;
    group.reserve(8);
    StateCompressNode<ADDR>* stateCompressNode = mkCompressTree(group, Target_Addr, Target_Tag, avoid);
    if (stateCompressNode) {
        if (group.size() == 0) {
            return;
        }else if (group.size() == 1) {
            Vns avoid_asserts(m_ctx, 1, 1);
            std::hash_map<ADDR, Vns> change_map; 
            bool child_has_branch = false;
            if (treeCompress(avoid_asserts, child_has_branch, change_map, stateCompressNode, 0, m_ctx, 0)) {
                if (child_has_branch) {
                    State* compress_state = ForkState(Target_Addr);
                    compress_state->set_changes(change_map, z3::solver::translate{});
                    compress_state->_StateCompressMkSymbol(*group[0]);
                    compress_state->solv.add_assert(avoid_asserts, false);
                    if (!compress_state->_StateCompression(*group[0])) {
                        VPANIC("State::StateCompressMkSymbol that you implement error");
                    }
                    branch.emplace_back(compress_state);
                    if (delete_avoid_state(stateCompressNode)) {
                        delete stateCompressNode;
                    }
                }
                else {
                    branchChunks.clear();
                    mem.clearRecord();
                    regs.clearRecord();
                    solv.add_assert(avoid_asserts, false);
                    _StateCompressMkSymbol(*group[0]);
                    if (delete_avoid_state(stateCompressNode)) {
                        delete stateCompressNode;
                    }
                    vassert(branch.empty());
                    set_changes(change_map);
                    guest_start = Target_Addr;
                    status = NewState;
                }
            }
            else {
                VPANIC("no compress");
            }

        }
        else {
            for (UInt gp = 0; gp < group.size(); gp++) {
                State* compress_state = ForkState(Target_Addr);
                std::hash_map<ADDR, Vns> change_map;
                Vns avoid_asserts(compress_state->m_ctx, 1, 1);
                bool child_has_branch = false;
                if (treeCompress(avoid_asserts, child_has_branch, change_map, stateCompressNode, gp, compress_state->m_ctx, 0)) {
                    compress_state->set_changes(change_map);
                    compress_state->_StateCompressMkSymbol(*group[gp]);
                    compress_state->solv.add_assert(avoid_asserts, false);
                    if (!compress_state->_StateCompression(*group[gp])) {
                        VPANIC("State::StateCompressMkSymbol that you implement error");
                    }
                    branch.emplace_back(compress_state);
                }
                else {
                    VPANIC("no compress");
                }
            }
            if (delete_avoid_state(stateCompressNode)) {
                delete stateCompressNode;
            }
        }
    }
}



inline Vns  TRsolver::getassert(z3::context& ctx) {
    return getassert().translate(ctx);
}

inline Vns  TRsolver::getassert() {
    Z3_context m_ctx = this->ctx();
    if (m_asserts.empty()) {
        VPANIC("impossible assertions num is zero");
    }
    if (m_asserts.size() == 1) {
        return m_asserts[0];
    }
    auto it = m_asserts.begin();
    auto end = m_asserts.end();
    Z3_ast* args = (Z3_ast*)malloc(sizeof(Z3_ast) * m_asserts.size());
    UInt i = 0;
    while (it != end) {
        args[i++] = it->operator Z3_ast();
        it++;
    }
    Vns re = Vns(m_ctx, Z3_mk_and(m_ctx, m_asserts.size(), args), 1);
    free(args);
    return re;
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
template void State<Addr32>::compress(Addr32 Target_Addr, State_Tag Target_Tag, std::vector<State_Tag>& avoid);
template void State<Addr64>::compress(Addr64 Target_Addr, State_Tag Target_Tag, std::vector<State_Tag>& avoid);
template State<Addr32>* State<Addr32>::mkChildState(BranchChunk const& bc);
template State<Addr64>* State<Addr64>::mkChildState(BranchChunk const& bc);
template State<Addr32>::operator std::string() const;
template State<Addr64>::operator std::string() const;
template void State<Addr32>::start(Bool first_bkp_pass);
template void State<Addr64>::start(Bool first_bkp_pass);
