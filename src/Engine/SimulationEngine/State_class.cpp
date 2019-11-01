#include "State_class.hpp"
#include "State_class.hpp"
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


#define vpanic(...) printf("%s line %d",__FILE__,__LINE__); vpanic(__VA_ARGS__);

#include "Z3_Target_Call/Z3_Target_Call.hpp"
#include "Z3_Target_Call/Guest_Helper.hpp"

#include "libvex_guest_x86.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_arm.h"
#include "libvex_guest_arm64.h"
#include "libvex_guest_mips32.h"
#include "libvex_guest_mips64.h"
#include "libvex_guest_ppc32.h"
#include "libvex_guest_ppc64.h"
#include "libvex_guest_s390x.h"


State*        _states[MAX_THREADS];
std::mutex global_state_mutex;

LARGE_INTEGER   freq_global = { 0 };
LARGE_INTEGER   beginPerformanceCount_global = { 0 };
LARGE_INTEGER   closePerformanceCount_global = { 0 };


#if defined(GUEST_IS_64)
typedef ULong(*Function_6)(ULong, ULong, ULong, ULong, ULong, ULong);
typedef ULong(*Function_5)(ULong, ULong, ULong, ULong, ULong);
typedef ULong(*Function_4)(ULong, ULong, ULong, ULong);
typedef ULong(*Function_3)(ULong, ULong, ULong);
typedef ULong(*Function_2)(ULong, ULong);
typedef ULong(*Function_1)(ULong);
typedef ULong(*Function_0)();
#else
typedef ULong(*Function_6)(UInt, UInt, UInt, UInt, UInt, UInt);
typedef ULong(*Function_5)(UInt, UInt, UInt, UInt, UInt);
typedef ULong(*Function_4)(UInt, UInt, UInt, UInt);
typedef ULong(*Function_3)(UInt, UInt, UInt);
typedef ULong(*Function_2)(UInt, UInt);
typedef ULong(*Function_1)(UInt);
typedef ULong(*Function_0)();
#endif

typedef Vns (*Z3_Function6)(Vns &, Vns &, Vns &, Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function5)(Vns &, Vns &, Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function4)(Vns &, Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function3)(Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function2)(Vns &, Vns &);
typedef Vns (*Z3_Function1)(Vns &);



unsigned char fastalignD1[257];
unsigned char fastalign[257];
ULong fastMask[65];
ULong fastMaskI1[65];
ULong fastMaskB[9];
ULong fastMaskBI1[9];
ULong fastMaskReverse[65];
ULong fastMaskReverseI1[65];
__m256i m32_fast[33];
__m256i m32_mask_reverse[33];

tinyxml2::XMLDocument StatetTraceFlag::doc = tinyxml2::XMLDocument();
std::hash_map<ADDR, Hook_struct> State::CallBackDict;
std::hash_map<ADDR/*static table base*/, TRtype::TableIdx_CB> State::TableIdxDict;
ThreadPool* State::pool;
Vns State::ir_temp[MAX_THREADS][400];

__attribute__((noreturn))
void failure_exit() {
    QueryPerformanceCounter(&closePerformanceCount_global);
    double delta_seconds = (double)(closePerformanceCount_global.QuadPart - beginPerformanceCount_global.QuadPart) / freq_global.QuadPart;
    printf("failure_exit  %s line:%d spend %f \n", __FILE__, __LINE__, delta_seconds);
    throw (z3::exception("failure_exit exception  "));
}

void _vex_log_bytes(const HChar* bytes, SizeT nbytes) {
    std::cout << bytes;
}


void vex_hwcaps_vai(VexArch arch, VexArchInfo* vai) {
    switch (arch) {
    case VexArchX86:
        vai->hwcaps = VEX_HWCAPS_X86_MMXEXT |
            VEX_HWCAPS_X86_SSE1 |
            VEX_HWCAPS_X86_SSE2 |
            VEX_HWCAPS_X86_SSE3 |
            VEX_HWCAPS_X86_LZCNT;
        break;
    case VexArchAMD64:
        vai->hwcaps =
            VEX_HWCAPS_AMD64_SSE3 |
            VEX_HWCAPS_AMD64_SSSE3 |
            VEX_HWCAPS_AMD64_CX16 |
            VEX_HWCAPS_AMD64_LZCNT |
            VEX_HWCAPS_AMD64_AVX |
            VEX_HWCAPS_AMD64_RDTSCP |
            VEX_HWCAPS_AMD64_BMI |
            VEX_HWCAPS_AMD64_AVX2;
        break;
    case VexArchARM:
        vai->hwcaps = VEX_ARM_ARCHLEVEL(8) |
            VEX_HWCAPS_ARM_NEON |
            VEX_HWCAPS_ARM_VFP3;
        break;
    case VexArchARM64:
        vai->hwcaps = 0;
        vai->arm64_dMinLine_lg2_szB = 6;
        vai->arm64_iMinLine_lg2_szB = 6;
        break;
    case VexArchPPC32:
        vai->hwcaps = VEX_HWCAPS_PPC32_F |
            VEX_HWCAPS_PPC32_V |
            VEX_HWCAPS_PPC32_FX |
            VEX_HWCAPS_PPC32_GX |
            VEX_HWCAPS_PPC32_VX |
            VEX_HWCAPS_PPC32_DFP |
            VEX_HWCAPS_PPC32_ISA2_07;
        vai->ppc_icache_line_szB = 32;
        break;
    case VexArchPPC64:
        vai->hwcaps = VEX_HWCAPS_PPC64_V |
            VEX_HWCAPS_PPC64_FX |
            VEX_HWCAPS_PPC64_GX |
            VEX_HWCAPS_PPC64_VX |
            VEX_HWCAPS_PPC64_DFP |
            VEX_HWCAPS_PPC64_ISA2_07;
        vai->ppc_icache_line_szB = 64;
        break;
    case VexArchS390X:
        vai->hwcaps = 0;
        break;
    case VexArchMIPS32:
    case VexArchMIPS64:
        vai->hwcaps = VEX_PRID_COMP_CAVIUM;
        break;
    default:
        std::cout << "Invalid arch in vex_prepare_vai.\n" << std::endl;
        break;
    }
}
void vex_prepare_vbi(VexArch arch, VexAbiInfo* vbi) {
    // only setting the guest_stack_redzone_size for now
    // this attribute is only specified by the X86, AMD64 and PPC64 ABIs

    switch (arch) {
    case VexArchX86:
        vbi->guest_stack_redzone_size = 0;
        break;
    case VexArchAMD64:
        vbi->guest_stack_redzone_size = 128;
        break;
    case VexArchPPC64:
        vbi->guest_stack_redzone_size = 288;
        break;
    default:
        break;
    }
}

UInt needs_self_check(void* callback_opaque, VexRegisterUpdates* pxControl, const VexGuestExtents* guest_extents) {
    //std::cout << "needs_self_check\n" << std::endl;
    return 0;
}

void* dispatch(void) {
    std::cout << "dispatch\n" << std::endl;
    return NULL;
}

Bool chase_into_ok(void* value, Addr addr) {
    std::cout << value << addr << std::endl;
    return True;
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

Bool TriggerBug_is_init = False;
extern void Func_Map_Init();
void IR_init(VexControl& vc) {
    if (!TriggerBug_is_init) {
        Func_Map_Init();
        vassert(!vex_initdone);
        QueryPerformanceFrequency(&freq_global);
        QueryPerformanceCounter(&beginPerformanceCount_global);
        register_tid(GetCurrentThreadId());
        LibVEX_Init(&failure_exit, &_vex_log_bytes, 0/*debuglevel*/, &vc);
        unregister_tid(GetCurrentThreadId());

        for (int i = 0; i < 257; i++) fastalignD1[i] = (((((i)-1) & -8) + 8) >> 3) - 1;
        for (int i = 0; i < 257; i++) fastalign[i] = (((((i)-1) & -8) + 8) >> 3);
        for (int i = 0; i <= 64; i++) fastMask[i] = (1ull << i) - 1; fastMask[64] = -1ULL;
        for (int i = 0; i <= 64; i++) fastMaskI1[i] = (1ull << (i + 1)) - 1; fastMaskI1[63] = -1ULL; fastMaskI1[64] = -1ULL;
        for (int i = 0; i <= 7; i++) fastMaskB[i] = (1ull << (i << 3)) - 1; fastMaskB[8] = -1ULL;
        for (int i = 0; i <= 7; i++) fastMaskBI1[i] = (1ull << ((i + 1) << 3)) - 1; fastMaskBI1[7] = -1ULL;
        for (int i = 0; i <= 64; i++) fastMaskReverse[i] = ~fastMask[i];
        for (int i = 0; i <= 64; i++) fastMaskReverseI1[i] = ~fastMaskI1[i];

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
    TriggerBug_is_init = True;
}


int eval_all(std::vector<Z3_ast>& result, solver& solv, Z3_ast nia) {
    //std::cout << nia << std::endl;
    //std::cout << state.solv.assertions() << std::endl;
    result.reserve(20);
    solv.push();
    std::vector<Z3_model> mv;
    mv.reserve(20);
    register Z3_context ctx = solv.ctx();
    for (int nway = 0; ; nway++) {
        Z3_lbool b = Z3_solver_check(ctx, solv);
        if (b == Z3_L_TRUE) {
            Z3_model m_model = Z3_solver_get_model(ctx, solv);
            Z3_model_inc_ref(ctx, m_model);
            mv.emplace_back(m_model);
            Z3_ast r = 0;
            bool status = Z3_model_eval(ctx, m_model, nia, /*model_completion*/false, &r);
            Z3_inc_ref(ctx, r);
            result.emplace_back(r);
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
        }
        else {
#if defined(OPSTR)
            //std::cout << "     sizeof symbolic : " << result.size() ;
            for (auto s : result) std::cout << ", " << Z3_ast_to_string(ctx, s);
#endif
            solv.pop();
            for (auto m : mv) Z3_model_dec_ref(ctx, m);

            return result.size();
        }
    }
}

static unsigned char* _n_page_mem(void* pap) {
    return ((State*)(((Pap*)(pap))->state))->mem.get_next_page(((Pap*)(pap))->guest_addr);
}

State::State(const char *filename, Addr64 gse, Bool _need_record) :
    Vex_Info(filename),
    m_ctx(), 
    m_params(m_ctx),
    m_tactic(with(tactic(m_ctx, "simplify"), m_params) &
        tactic(m_ctx, "sat")&
        tactic(m_ctx, "solve-eqs")&
        tactic(m_ctx, "bit-blast")&
        tactic(m_ctx, "smt")
    ),
    mem(*this, &m_ctx,need_record),
    regs(m_ctx, need_record), 
    //solv(m_ctx),
    solv(m_tactic.mk_solver()),
    need_record(_need_record),
    status(NewState),
    VexGuestARCHState(NULL),
    delta(0),
    unit_lock(true),
    replace_const(0),
    isTop(True)
{
    m_params.set("mul2concat", true);
 
    pap.state = (void*)(this);
    pap.n_page_mem = _n_page_mem;
    assert(MaxThreadsNum <= MAX_THREADS);
    if (pool) 
        delete pool;
    pool = new ThreadPool(MaxThreadsNum);

    asserts.resize(5);
    branch.reserve(10);
    init_threads_id(); 
    tempmeminit(); 
    IR_init(vc);
    
    read_mem_dump(MemoryDumpPath);
    if (gse)
        guest_start_ep = gse;
    else {
        if (GuestStartAddress!=-1) {
            guest_start_ep = GuestStartAddress;
            if (!guest_start_ep) {
                goto mem_ip;
            }
        }
        else {
mem_ip:
            guest_start_ep = regs.Iex_Get(RegsIpOffset, Ity_I64);
        }
    }
    guest_start = guest_start_ep;
};


State::State(State *father_state, Addr64 gse) :
    Vex_Info(*father_state),
    m_ctx(),
    m_params(m_ctx),
    m_tactic(with(tactic(m_ctx, "simplify"), m_params)&
        tactic(m_ctx, "sat")&
        tactic(m_ctx, "solve-eqs")&
        tactic(m_ctx, "bit-blast")&
        tactic(m_ctx, "smt")
    ),
    mem(*this, father_state->mem, &m_ctx, need_record),
    guest_start_ep(gse),
    guest_start(guest_start_ep), 
    solv(m_ctx, father_state->solv,  z3::solver::translate{}),
    regs(father_state->regs, m_ctx, need_record),
    need_record(father_state->need_record),
    status(NewState),
    VexGuestARCHState(NULL),
    delta(0),
    unit_lock(true),
    replace_const(father_state->replace_const),
    isTop(False)
{

    pap.state = (void*)(this);
    pap.n_page_mem = _n_page_mem;
    IR_init(vc);
};

State::~State() { 
    if (VexGuestARCHState) delete VexGuestARCHState;
    if(branch.size())
        for (auto s : branch){
            delete s;
        }
}


State::operator std::string(){
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
        snprintf(hex, sizeof(hex),  "%llx    \n}\n ", guest_start_ep);
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

inline Vns State::getassert(z3::context &ctx) {
    if (asserts.empty()) {
        vpanic("impossible assertions num is zero");
    }
    auto it = asserts.begin();
    auto end = asserts.end();
    auto result = *it;
    it ++;
    while (it != end) {
        result = result && *it;
        it ++;
    }
    return result.translate(ctx).simplify();
}

inline std::ostream & operator<<(std::ostream & out, State & n) {
    return out<< (std::string)n;
}

Vns State::get_int_const(UShort nbit) {
    bool xchgbv = false;
    while (!xchgbv) {
        __asm__ __volatile("xchgb %b0,%1":"=r"(xchgbv) : "m"(unit_lock), "0"(xchgbv) : "memory");
    };
    auto res = replace_const++;
    unit_lock = true;
    char buff[20];
    sprintf_s(buff, sizeof(buff), "part_%lx_%d",guest_start, res);
    return  Vns(m_ctx.bv_const(buff, nbit), nbit);
}


void State::hook_add(ADDR addr, TRtype::Hook_CB func)
{
    if (CallBackDict.find(addr) == CallBackDict.end()) {
        auto P = mem.getMemPage(addr);
        CallBackDict[addr] = Hook_struct{ func ,P->unit->m_bytes[addr & 0xfff] };
        P->unit->m_bytes[addr & 0xfff] = 0xCC;
    }
    else {
        CallBackDict[addr].cb = func;
    }
}

void State::hook_del(ADDR addr, TRtype::Hook_CB func)
{
    if (CallBackDict.find(addr) == CallBackDict.end()) {
    }
    else {
        pool->wait();
        auto P = mem.getMemPage(addr);
        P->unit->m_bytes[addr & 0xfff] = CallBackDict[addr].original;
        CallBackDict.erase(CallBackDict.find(addr));
    }
}

Z3_ast State::idx2Value(ADDR base, Z3_ast idx)
{
    auto _where = State::TableIdxDict.lower_bound((ADDR)base);
    if (_where != State::TableIdxDict.end()) {
        //vex_printf("pycfun: %p \n", _where->second);
        return _where->second(this, (Addr64)base, (Z3_ast)idx);
    }
    else
    {
        return (Z3_ast)NULL;
    }
}


inline IRSB* State::BB2IR() {
    mem.set_double_page(guest_start, pap);
    pap.start_swap       = 0;
    vta.guest_bytes      = (UChar *)(pap.t_page_addr);
    vta.guest_bytes_addr = (Addr64)((ADDR)guest_start);
    IRSB *irsb;
    if(0){
        printf("GUESTADDR %16llx   RUND:%ld CODES   ", guest_start, runed);
        TESTCODE(
            irsb = LibVEX_FrontEnd(&vta, &res, &pxControl);
        );
    }
    else {
        return LibVEX_FrontEnd(&vta, &res, &pxControl);
    }
    return irsb;
}




inline void State::add_assert(Vns & assert,Bool ToF)
{
    assert = assert.simplify();
    if(assert.is_bool()){
        if (ToF) {
            Z3_solver_assert(m_ctx, solv, assert);
            asserts.push_back(assert);
        }
        else {
            auto not = !  assert;
            Z3_solver_assert(m_ctx, solv, not);
            asserts.push_back(not);
        }
    }
    else {
        auto ass = (assert == (Bool)ToF);
        Z3_solver_assert(m_ctx, solv, ass);
        asserts.push_back(ass);
    }
}

inline void State::add_assert_eq(Vns & eqA, Vns & eqB)
{
    Vns ass = (eqA == eqB).simplify();
    Z3_solver_assert(m_ctx, solv, ass);
    asserts.push_back(ass);
}

inline void State::write_regs(int offset, void* addr, int length) { regs.write_regs(offset, addr, length); }
inline void State::read_regs(int offset, void* addr, int length) { regs.read_regs(offset, addr, length); }

inline Vns symbolic_check(Z3_context ctx, ULong ret, UInt bitn) {
    if (ret & (0xfa1dull << 48)) {
        return Vns(ctx, (Z3_ast)(ret & ((1ull << 48) - 1)), bitn);
    }
    else {
        return Vns(ctx, ret, bitn);
    }
}

inline Vns State::CCall(IRCallee *cee, IRExpr **exp_args, IRType ty)
{
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    UShort bitn = ty2bit(ty);
    Bool z3_mode = False;
    if (!exp_args[0]) return Vns(m_ctx, ((Function_0)(cee->addr))(), bitn);
    Vns arg0 = tIRExpr(exp_args[0]);
    if (arg0.symbolic()) z3_mode = True;
    if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(funcDict(cee->addr)))(arg0) : symbolic_check(m_ctx, ((Function_1)(cee->addr))(arg0), bitn);
    Vns arg1 = tIRExpr(exp_args[1]);
    if (arg1.symbolic()) z3_mode = True;
    if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(funcDict(cee->addr)))(arg0, arg1) : symbolic_check(m_ctx, ((Function_2)(cee->addr))(arg0, arg1), bitn);
    Vns arg2 = tIRExpr(exp_args[2]);
    if (arg2.symbolic()) z3_mode = True;
    if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(funcDict(cee->addr)))(arg0, arg1, arg2) : symbolic_check(m_ctx, ((Function_3)(cee->addr))(arg0, arg1, arg2), bitn);
    Vns arg3 = tIRExpr(exp_args[3]);
    if (arg3.symbolic()) z3_mode = True;
    if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(funcDict(cee->addr)))(arg0, arg1, arg2, arg3) : symbolic_check(m_ctx, ((Function_4)(cee->addr))(arg0, arg1, arg2, arg3), bitn);
    Vns arg4 = tIRExpr(exp_args[4]);
    if (arg4.symbolic()) z3_mode = True;
    if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(funcDict(cee->addr)))(arg0, arg1, arg2, arg3, arg4) : symbolic_check(m_ctx, ((Function_5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), bitn);
    Vns arg5 = tIRExpr(exp_args[5]);
    if (arg5.symbolic()) z3_mode = True;
    if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(funcDict(cee->addr)))(arg0, arg1, arg2, arg3, arg4, arg5) : symbolic_check(m_ctx, ((Function_6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), bitn);
}


inline void State::thread_register()
{
    traceStart();
    {
        std::unique_lock<std::mutex> lock(global_state_mutex);
        register_tid(GetCurrentThreadId());
    }
    auto i = temp_index();
    _states[i] = this;
    for (int j = 0; j < 400; j++) {
        ir_temp[i][j].m_kind = REAL;
    }
}
inline void State::thread_unregister()
{
    auto i = temp_index();
    for (int j = 0; j < 400; j++) {
        ir_temp[i][j].~Vns();
    }
    {
        std::unique_lock<std::mutex> lock(global_state_mutex);
        unregister_tid(GetCurrentThreadId());
    }
    traceFinish();
}

void State::read_mem_dump(const char  *filename)
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
    unsigned long long length, fp, err, name_start_offset, name_end_offset;
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
    printf("+--------------------+--------------------+--------------------+------------+\n");
    printf("|         SN         |         VA         |         FOA        |     LEN    |\n");
    printf("+--------------------+--------------------+--------------------+------------+\n");
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
            printf("| %-18s |  %16llx  |  %16llx  | %10llx |\n", name, buf.address, buf.dataoffset, buf.length);
            if (err = mem.map(buf.address, buf.length))
                printf("warning %s had maped before length: %llx\n", name, err);
            mem.write_bytes(buf.address, buf.length, data);
        }
        fseek(infile, fp, SEEK_SET);
        free(data);
    }
    printf("+---------------------------------------------------------------------------+\n");
    free(name_buff);
    fclose(infile);
}

inline Vns State::ILGop(IRLoadG *lg) {
    switch (lg->cvt) {
    case ILGop_IdentV128:{ return mem.Iex_Load(tIRExpr(lg->addr), Ity_V128);            }
    case ILGop_Ident64:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I64 );            }
    case ILGop_Ident32:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I32 );            }
    case ILGop_16Uto32:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I16 ).zext(16);    }
    case ILGop_16Sto32:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I16 ).sext(16);    }
    case ILGop_8Uto32:   { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I8  ).sext(8);    }
    case ILGop_8Sto32:   { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I8  ).sext(8);    }
    case ILGop_INVALID:
    default: vpanic("ppIRLoadGOp");
    }
}




inline Vns State::tIRExpr(IRExpr* e)
{
    switch (e->tag) {
    case Iex_Get: { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
    case Iex_RdTmp: { return ir_temp[t_index][e->Iex.RdTmp.tmp]; }
    case Iex_Unop: { return T_Unop(e->Iex.Unop.op, e->Iex.Unop.arg); }
    case Iex_Binop: { return T_Binop(e->Iex.Binop.op, e->Iex.Binop.arg1, e->Iex.Binop.arg2); }
    case Iex_Triop: { return T_Triop(e->Iex.Triop.details->op, e->Iex.Triop.details->arg1, e->Iex.Triop.details->arg2, e->Iex.Triop.details->arg3); }
    case Iex_Qop: { return T_Qop(e->Iex.Qop.details->op, e->Iex.Qop.details->arg1, e->Iex.Qop.details->arg2, e->Iex.Qop.details->arg3, e->Iex.Qop.details->arg4); }
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
        if (!VexGuestARCHState) {
            switch (guest) {
            case VexArchX86: VexGuestARCHState = new VexGuestX86State; break;
            case VexArchAMD64: VexGuestARCHState = new _VexGuestAMD64State(*this); break;
            case VexArchARM: VexGuestARCHState = new VexGuestARMState; break;
            case VexArchARM64: VexGuestARCHState = new VexGuestARM64State; break;
            case VexArchMIPS32: VexGuestARCHState = new VexGuestMIPS32State; break;
            case VexArchMIPS64: VexGuestARCHState = new VexGuestMIPS64State; break;
            case VexArchPPC32: VexGuestARCHState = new VexGuestPPC32State; break;
            case VexArchPPC64: VexGuestARCHState = new VexGuestPPC64State; break;
            case VexArchS390X: VexGuestARCHState = new VexGuestS390XState; break;
            default:vpanic("not support");
            }
        }
        return Vns(m_ctx, VexGuestARCHState);
    };
    case Iex_VECRET:
    case Iex_Binder:
    default:
        vex_printf("tIRExpr error:  %d", e->tag);
        vpanic("not support");
    }
}




void State::start(Bool first_bkp_pass) {
    if (this->status != NewState) {
        vex_printf("this->status != NewState");
        return;
    }
    Bool is_first_bkp_pass = False;
    Addr64 hook_bkp = NULL;
    status = Running;
    thread_register();
    t_index = temp_index();
    Vns* irTemp = ir_temp[t_index]; 
    this->is_dynamic_block = false;

Begin_try:

    try {
        try {
            if(first_bkp_pass)
                if ((UChar)mem.Iex_Load<Ity_I8>(guest_start) == 0xCC) {
                    is_first_bkp_pass = True;
                    goto bkp_pass;
                }
            for (;;) {
For_Begin:
                IRSB* irsb = BB2IR();
                traceIRSB(irsb);
                guest_start_of_block = guest_start;
                //ppIRSB(irsb);
For_Begin_NO_Trans:
                for (UInt stmtn = 0; stmtn < irsb->stmts_used; stmtn++) {
                    IRStmt *s = irsb->stmts[stmtn];
                    traceIRStmtBegin(s);
                    switch (s->tag) {
                    case Ist_Put: { regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
                    case Ist_Store: { mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; };
                    case Ist_WrTmp: { irTemp[s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data); break; };
                    case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
                        bool xchgbv = false;
                        while (!xchgbv) { __asm__ __volatile("xchgb %b0,%1":"=r"(xchgbv) : "m"(unit_lock), "0"(xchgbv) : "memory"); }
                        IRCAS cas = *(s->Ist.CAS.details);
                        Vns addr = tIRExpr(cas.addr);//r10.value
                        Vns expdLo = tIRExpr(cas.expdLo);
                        Vns dataLo = tIRExpr(cas.dataLo);
                        if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
                            Vns expdHi = tIRExpr(cas.expdHi);
                            Vns dataHi = tIRExpr(cas.dataHi);
                            irTemp[cas.oldHi] = mem.Iex_Load(addr, length2ty(expdLo.bitn));
                            irTemp[cas.oldLo] = mem.Iex_Load(addr, length2ty(expdLo.bitn));
                            mem.Ist_Store(addr, dataLo);
                            mem.Ist_Store(addr + (dataLo.bitn >> 3), dataHi);
                        }
                        else {//single
                            irTemp[cas.oldLo] = mem.Iex_Load(addr, length2ty(expdLo.bitn));
                            mem.Ist_Store(addr, dataLo);
                        }
                        unit_lock = true;
                        break;
                    }
                    case Ist_Exit: {
                        Vns guard = tIRExpr(s->Ist.Exit.guard);
                        if (guard.real()) {
                            if ((UChar)guard) {
Exit_guard_true:
                                if (s->Ist.Exit.jk != Ijk_Boring
                                    && s->Ist.Exit.jk != Ijk_Call
                                    && s->Ist.Exit.jk != Ijk_Ret
                                    )
                                {
                                    ppIRSB(irsb);
                                    status = Ijk_call(s->Ist.Exit.jk);
                                    if (status != Running) {
                                        goto EXIT;
                                    }
                                    if (delta) {
                                        guest_start = guest_start + delta;
                                        delta = 0;
                                        goto For_Begin;
                                    }
                                }
                                else {
                                    guest_start = s->Ist.Exit.dst->Ico.U64;
                                    hook_bkp = NULL;
                                    goto For_Begin;
                                }
                            }
                            break;
                        }
                        else {
                            int rgurd[2];
                            std::vector<Z3_ast> guard_result;
                            int num_guard = eval_all(guard_result, solv, guard);
                            if (num_guard == 1) {
                                Z3_get_numeral_int(m_ctx, guard_result[0], &rgurd[0]);
                                Z3_dec_ref(m_ctx, guard_result[0]);
                                if (rgurd[0]) {
                                    add_assert(guard, True);
                                    goto Exit_guard_true;
                                }
                                else {
                                    add_assert(guard, False);
                                }
                            }
                            else if (num_guard == 2) {
                                Z3_dec_ref(m_ctx, guard_result[0]);
                                Z3_dec_ref(m_ctx, guard_result[1]);
                                struct _bs {
                                    ADDR addr;
                                    Z3_ast _s_addr;
                                    bool _not;
                                };
                                std::vector<_bs> bs_v;
                                bs_v.emplace_back(_bs{ s->Ist.Exit.dst->Ico.U64 ,NULL, True });

                                Vns _next = tIRExpr(irsb->next);
                                if (stmtn == irsb->stmts_used - 1) {
                                    if (_next.real()) {
                                        bs_v.emplace_back(_bs{ _next ,_next, False });
                                    }
                                    else {
                                        std::vector<Z3_ast> next_result;
                                        eval_all(next_result, solv, _next);
                                        for (auto&& re : next_result) {
                                            uint64_t r_next;
                                            Z3_get_numeral_uint64(m_ctx, re, &r_next);
                                            bs_v.emplace_back(_bs{ r_next ,_next, False });
                                        }
                                    }
                                }
                                else {
                                    while (irsb->stmts[stmtn]->tag != Ist_IMark) { stmtn--; };
                                    bs_v.emplace_back(_bs{ guest_start + irsb->stmts[stmtn]->Ist.IMark.len , NULL, False });
                                }
                                
                                for (auto && _bs : bs_v) {
                                    State *state = ForkState(_bs.addr);
                                    if (state) {
                                        branch.emplace_back(state);
                                        state->add_assert(guard.translate(*state), _bs._not);
                                        if (_bs._s_addr) {
                                            auto _next_a = Vns(state->m_ctx, Z3_translate(m_ctx, _bs._s_addr, *state));
                                            auto _next_b = Vns(state->m_ctx, Z3_mk_unsigned_int64(state->m_ctx, _bs.addr, Z3_get_sort(state->m_ctx, _next_a)));
                                            state->add_assert_eq(_next_a, _next_b);
                                        }
                                    }
                                }
                                status = Fork; goto EXIT;
                            }
                            else {
                                status = Death; goto EXIT;
                            }
                        }
                    }
                    case Ist_NoOp: break;
                    case Ist_IMark: {
                        guest_start = (ADDR)s->Ist.IMark.addr; 
                        if (this->is_dynamic_block) {
                            this->is_dynamic_block = false;
                            goto For_Begin;// fresh changed block
                        }
                        break; 
                    };
                    case Ist_AbiHint:break; //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
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
                                s->Ist.PutI.details->descr->base + (((UInt)((s->Ist.PutI.details->bias + (int)(ix)))) % s->Ist.PutI.details->descr->nElems)*ty2length(s->Ist.PutI.details->descr->elemTy),
                                tIRExpr(s->Ist.PutI.details->data)
                            );
                        }
                        else {
                            vassert(0);
                        }
                        break;
                    }
                    case Ist_Dirty: {
                        IRDirty *dirty = s->Ist.Dirty.details;
                        auto guard = tIRExpr(dirty->guard);
                        if (((UChar)guard) & 1) {
                            auto k = CCall(dirty->cee, dirty->args, Ity_I64);
                            if (dirty->tmp != -1) {
                                irTemp[dirty->tmp] = k;
                            }
                        }
                        break;
                    }

                    case Ist_LoadG: {
                        IRLoadG *lg = s->Ist.LoadG.details;
                        auto guard = tIRExpr(lg->guard);
                        if (guard.real()) {
                            irTemp[lg->dst] = (((UChar)guard)) ? ILGop(lg) : tIRExpr(lg->alt);
                        }
                        else {
                            irTemp[lg->dst] = ite(guard == 1, ILGop(lg), tIRExpr(lg->alt));
                        }
                        break;
                    }
                    case Ist_StoreG: {
                        IRStoreG *sg = s->Ist.StoreG.details;
                        auto guard = tIRExpr(sg->guard);
                        if (guard.real()) {
                            if ((UChar)guard) 
                                mem.Ist_Store(tIRExpr(sg->addr), tIRExpr(sg->data));
                        }
                        else {
                            auto addr = tIRExpr(sg->addr);
                            auto data = tIRExpr(sg->data);
                            mem.Ist_Store(addr, ite(guard == 1, mem.Iex_Load(addr, length2ty(data.bitn)), data));
                        }
                        break;
                    }
                    case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/
                    case Ist_LLSC:
                    default:
                        vex_printf("what ppIRStmt %d\n", s->tag);
                        vpanic("what ppIRStmt");
                    }

                    traceIRStmtEnd(s);
                }

                switch (irsb->jumpkind) {
                case Ijk_Boring:        break;
                case Ijk_Call:            break;
                case Ijk_Ret:           break;
                case Ijk_SigTRAP:        {
bkp_pass:
                    auto _where = CallBackDict.lower_bound((ADDR)guest_start);
                    if (_where != CallBackDict.end()) {
                        if (hook_bkp) {
                            guest_start = hook_bkp;
                            hook_bkp = NULL;
                            goto For_Begin;
                        }
                        else {
                            if (!is_first_bkp_pass) {
                                if (_where->second.cb) {
                                    status = (_where->second.cb)(this);//State::delta maybe changed by callback
                                }
                                if (status != Running) {
                                    goto EXIT;
                                }
                            }
                            else {
                                is_first_bkp_pass = False;
                            }
                            if (delta) {
                                guest_start = guest_start + delta;
                                delta = 0;
                                goto For_Begin;
                            }
                            else {
                                __m256i m32 = mem.Iex_Load<Ity_V256>(guest_start);
                                m32.m256i_i8[0] = _where->second.original;
                                pap.start_swap = 2;
                                vta.guest_bytes = (UChar *)(&m32);
                                vta.guest_bytes_addr = (Addr64)((ADDR)guest_start);
                                auto max_insns = pap.guest_max_insns;
                                pap.guest_max_insns = 1;
                                irsb = LibVEX_FrontEnd(&vta, &res, &pxControl);
                                //ppIRSB(irsb);
                                pap.guest_max_insns = max_insns;
                                hook_bkp = (ADDR)guest_start + irsb->stmts[0]->Ist.IMark.len;
                                irsb->jumpkind = Ijk_SigTRAP;
                                goto For_Begin_NO_Trans;
                            }
                        }
                    }
                }
                case Ijk_NoDecode:{
                    vex_printf("Ijk_NoDecode: %p", guest_start);
                    status = NoDecode;
                    goto EXIT;
                }
/*Ijk_Sys_syscall, Ijk_ClientReq,Ijk_Yield, Ijk_EmWarn, Ijk_EmFail, Ijk_MapFail, Ijk_InvalICache, 
Ijk_FlushDCache, Ijk_NoRedir, Ijk_SigILL, Ijk_SigSEGV, Ijk_SigBUS, Ijk_SigFPE, Ijk_SigFPE_IntDiv, Ijk_SigFPE_IntOvf, 
Ijk_Sys_int32,Ijk_Sys_int128, Ijk_Sys_int129, Ijk_Sys_int130, Ijk_Sys_int145, Ijk_Sys_int210, Ijk_Sys_sysenter:*/
                default:
                    status = Ijk_call(irsb->jumpkind);
                    if (status != Running) {
                        goto EXIT;
                    }
                    if (delta) {
                        guest_start = guest_start + delta;
                        delta = 0;
                        goto For_Begin;
                    }
                }
Isb_next:
                Vns next = tIRExpr(irsb->next);
                if (next.real()) {
                    guest_start = next;
                }
                else {
                    std::vector<Z3_ast> result;
                    switch (eval_all(result, solv, next)) {
                    case 0: next.~Vns(); goto EXIT;
                    case 1:
                        uint64_t u64_Addr;
                        Z3_get_numeral_uint64(m_ctx, result[0], &u64_Addr);
                        guest_start = u64_Addr;
                        Z3_dec_ref(m_ctx, result[0]);
                        break;
                    default:
                        for (auto && re : result) {
                            uint64_t rgurd;
                            Z3_get_numeral_uint64(m_ctx, re, &rgurd);

                            State *state = ForkState(rgurd);
                            if (state) {
                                branch.emplace_back(state);
                                state->add_assert_eq(Vns(m_ctx, Z3_translate(m_ctx, re, *state)), next.translate(*state));
                            }
                            Z3_dec_ref(m_ctx, re);
                        }
                        status = Fork;
                        next.~Vns();
                        goto EXIT;
                    }
                }
            };

        }
        catch (...) {
            //SEH Exceptions (/EHa)
            try {
                cpu_exception();
                if (status = Death) {
                    std::cout << "W MEM ERR at " << std::hex << guest_start << std::endl;
                    status = Death;
                }
            }
            catch (...) {
                std::cout << "W MEM ERR at " << std::hex << guest_start << std::endl;
                status = Death;
            }
        }
    }
    catch (exception &error) {
        vex_printf("unexpected z3 error: at %llx\n", guest_start);
        std::cout << error << std::endl;
        status = Death;
    }
    
    if (status == Exception) {
        status = Running;
        goto Begin_try;
    }


EXIT:
    unit_lock = true;
    thread_unregister();
}

void State::branchGo()
{
    for(auto b : branch){
        State::pool->enqueue([b] {
            b->start(True);
            });
    }
}


template<class TC>
inline void StatePrinter<TC>::spIRExpr(const IRExpr* e)

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
        vpanic("ppIRExpr");
    }
}

template<class TC>
void StatePrinter<TC>::spIRPutI(const IRPutI* puti)
{
    vex_printf("PUTI");
    ppIRRegArray(puti->descr);
    vex_printf("[");
    ppIRExpr(puti->ix);
    vex_printf(",%d] = ", puti->bias);
    ppIRExpr(puti->data);
}

template<class TC>
void StatePrinter<TC>::spIRStmt(const IRStmt* s)

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
        vpanic("ppIRStmt");
    }
}

#include "Compress.hpp"


#include "Unop.hpp"
#include "Binop.hpp"
#include "Triop.hpp"
#include "Qop.hpp"




