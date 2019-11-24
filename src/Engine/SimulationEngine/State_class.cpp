
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



  UChar fastalignD1[257];
  UChar fastalign[257];
  ULong fastMask[65];
  ULong fastMaskI1[65];
  ULong fastMaskB[9];
  ULong fastMaskBI1[9];
  ULong fastMaskReverse[65];
  ULong fastMaskReverseI1[65];
__m256i m32_fast[33];
__m256i m32_mask_reverse[33];





tinyxml2::XMLDocument Vex_Info::doc = tinyxml2::XMLDocument();
VexRegisterUpdates Vex_Info::iropt_register_updates_default = VexRegUpdSpAtMemAccess;
Int Vex_Info::iropt_level = 2;
UInt Vex_Info::guest_max_insns = 100;
tinyxml2::XMLError Vex_Info::err = tinyxml2::XML_ERROR_COUNT;
tinyxml2::XMLElement* Vex_Info::doc_TriggerBug = nullptr;
tinyxml2::XMLElement* Vex_Info::doc_VexControl = nullptr;
tinyxml2::XMLElement* Vex_Info::doc_debug = nullptr;
GuestSystem Vex_Info::guest_system = unknowSystem;
VexArch Vex_Info::guest = VexArch_INVALID;
const char* Vex_Info::MemoryDumpPath = "你没有这个文件";
ADDR Vex_Info::GuestStartAddress = 0;
UInt Vex_Info::MaxThreadsNum = 16;
Int Vex_Info::traceflags = 0;


std::hash_map<ADDR, Hook_struct> State::CallBackDict;
std::hash_map<ADDR/*static table base*/, TRtype::TableIdx_CB> State::TableIdxDict;
ThreadPool* State::pool;
Vns State::ir_temp[MAX_THREADS][MAX_IRTEMP];

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

extern void Func_Map_Init();
void IR_init(VexControl& vc) {
    QueryPerformanceFrequency(&freq_global);
    QueryPerformanceCounter(&beginPerformanceCount_global);
    if (!vex_initdone) {
        Func_Map_Init();
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
}


int eval_all(std::vector<Vns>& result, solver& solv, Z3_ast nia) {
    //std::cout << nia << std::endl;
    //std::cout << state.solv.assertions() << std::endl;
    result.reserve(20);
    solv.push();
    std::vector<Z3_model> mv;
    mv.reserve(20);
    Z3_context ctx = solv.ctx();
    for (int nway = 0; ; nway++) {
        Z3_lbool b = Z3_solver_check(ctx, solv);
        if (b == Z3_L_TRUE) {
            Z3_model m_model = Z3_solver_get_model(ctx, solv);
            Z3_model_inc_ref(ctx, m_model);
            mv.emplace_back(m_model);
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
        }
        else {
#if defined(OPSTR)
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

State::State(const char *filename, ADDR gse, Bool _need_record) :
    Vex_Info(filename),
    m_ctx(), 
    m_params(m_ctx),
    m_tactic(with(tactic(m_ctx, "simplify"), m_params) &
        tactic(m_ctx, "sat")&
        tactic(m_ctx, "solve-eqs")&
        tactic(m_ctx, "bit-blast")&
        tactic(m_ctx, "smt")
        /*&
        tactic(m_ctx, "factor")&
        tactic(m_ctx, "bv1-blast")&
        tactic(m_ctx, "qe-sat")&
        tactic(m_ctx, "ctx-solver-simplify")&
        tactic(m_ctx, "nla2bv")&
        tactic(m_ctx, "symmetry-reduce")*/
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
            guest_start_ep = regs.Iex_Get(gRegsIpOffset(), Ity_I64);
        }
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


State::State(State *father_state, ADDR gse) :
    Vex_Info(*father_state),
    m_ctx(),
    m_params(m_ctx),
    m_tactic(m_ctx, "smt"),
    mem(*this, father_state->mem, &m_ctx, father_state->need_record),
    guest_start_ep(gse),
    guest_start(guest_start_ep), 
    solv(m_ctx, father_state->solv,  z3::solver::translate{}),
    regs(father_state->regs, m_ctx, father_state->need_record),
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

bool State::get_hook(Hook_struct& hs, ADDR addr)
{
    auto _where = CallBackDict.lower_bound((ADDR)guest_start);
    if (_where == CallBackDict.end()) {
        return false;
    }
    hs = _where->second;
    return true;
}

inline Vns State::getassert(z3::context &ctx) {
    if (asserts.empty()) {
        vpanic("impossible assertions num is zero");
    }
    auto it = asserts.begin();
    auto end = asserts.end();
    Z3_ast* args = (Z3_ast*)malloc(sizeof(Z3_ast) * asserts.size());
    UInt i = 0;
    while (it != end) {
        args[i++] = it->operator Z3_ast();
        it++;
    }
    Vns re = Vns(m_ctx, Z3_mk_and(m_ctx, asserts.size(), args), 1).translate(ctx);
    free(args);
    return re;
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
    sprintf_s(buff, sizeof(buff), "p_%d", res);
    return  Vns(m_ctx.bv_const(buff, nbit), nbit);
}

Vns State::get_int_const(UShort n, UShort nbit) {
    char buff[20];
    sprintf_s(buff, sizeof(buff), "p_%d", n);
    return  Vns(m_ctx.bv_const(buff, nbit), nbit);
}


UInt State::getStr(std::stringstream& st, ADDR addr)
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
    VexRegisterUpdates pxControl;
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




void State::add_assert(Vns & assert,Bool ToF)
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
        Z3_ast ret_ast = (Z3_ast)(ret & ((1ull << 48) - 1));
        vassert(Z3_get_bv_sort_size(ctx, Z3_get_sort(ctx, ret_ast)) == bitn);
        return Vns(ctx, ret_ast, bitn, no_inc{});
    }
    else {
        return Vns(ctx, ret, bitn);
    }
}


Vns State::CCall(IRCallee *cee, IRExpr **exp_args, IRType ty)
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
    {
        std::unique_lock<std::mutex> lock(global_state_mutex);
        register_tid(GetCurrentThreadId());
    }
    auto i = temp_index();
    for (int j = 0; j < MAX_IRTEMP; j++) {
        ir_temp[i][j].m_kind = REAL;
    }
}
inline void State::thread_unregister()
{
    auto i = temp_index();
    for (int j = 0; j < MAX_IRTEMP; j++) {
        ir_temp[i][j].~Vns();
    }
    {
        std::unique_lock<std::mutex> lock(global_state_mutex);
        unregister_tid(GetCurrentThreadId());
    }
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
    printf("/------------------------------+--------------------+--------------------+------------\\\n");
    printf("|              SN              |         VA         |         FOA        |     LEN    |\n");
    printf("+------------------------------+--------------------+--------------------+------------+\n");
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
            mem.write_bytes(buf.address, buf.length, data);
        }
        fseek(infile, fp, SEEK_SET);
        free(data);
    }
    printf("\\-------------------------------------------------------------------------------------/\n");
    free(name_buff);
    fclose(infile);
}
inline Vns State::ILGop(IRLoadG *lg) {
    switch (lg->cvt) {
    case ILGop_IdentV128:{ return mem.Iex_Load(tIRExpr(lg->addr), Ity_V128);            }
    case ILGop_Ident64:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I64 );            }
    case ILGop_Ident32:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I32 );            }
    case ILGop_16Uto32:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I16 ).zext(16);   }
    case ILGop_16Sto32:  { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I16 ).sext(16);   }
    case ILGop_8Uto32:   { return mem.Iex_Load(tIRExpr(lg->addr), Ity_I8  ).zext(8);    }
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
    status = Running;
    traceStart();
    thread_register();
    t_index = temp_index();
    _states[t_index] = this;
    Vns* irTemp = ir_temp[t_index]; 
    this->is_dynamic_block = false;
    Hook_struct hs;
    IRSB* irsb = nullptr;

Begin_try:
    try {
        try {
            if(first_bkp_pass)
                if ((UChar)mem.Iex_Load<Ity_I8>(guest_start) == 0xCC) {
                    if (get_hook(hs, guest_start)) {
                        setFlag(hs.cflag);
                        goto bkp_pass;
                    }
                    else {
                        goto SigTRAP;
                    }
                }

            for (;;) {
For_Begin:
                irsb = BB2IR();
                traceIRSB(irsb);
                //ppIRSB(irsb);
                goto For_Begin_NO_Trans;
            deal_bkp:
                {
                    if (hs.cb) {
                        status = (hs.cb)(this);//State::delta maybe changed by callback
                    }
                    if (status != Running) {
                        goto EXIT;
                    }
                    if (delta) {
                        guest_start = guest_start + delta;
                        delta = 0;
                        goto For_Begin;
                    }
                    else {
                    bkp_pass:
                        __m256i m32 = mem.Iex_Load<Ity_V256>(guest_start);
                        m32.m256i_i8[0] = hs.original;
                        pap.start_swap = 2;
                        vta.guest_bytes = (UChar*)(&m32);
                        vta.guest_bytes_addr = (Addr64)((ADDR)guest_start);
                        auto max_insns = pap.guest_max_insns;
                        pap.guest_max_insns = 1;
                        VexRegisterUpdates pxControl;
                        irsb = LibVEX_FrontEnd(&vta, &res, &pxControl);
                        //ppIRSB(irsb);
                        pap.guest_max_insns = max_insns;
                    }
                }
            For_Begin_NO_Trans:
                guest_start_of_block = guest_start;
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
                            irTemp[cas.oldHi] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                            irTemp[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                            mem.Ist_Store(addr, dataLo);
                            mem.Ist_Store(addr + (dataLo.bitn >> 3), dataHi);
                        }
                        else {//single
                            irTemp[cas.oldLo] = mem.Iex_Load(addr, (IRType)(expdLo.bitn));
                            mem.Ist_Store(addr, dataLo);
                        }
                        unit_lock = true;
                        break;
                    }
                    case Ist_Exit: {
                        Vns guard = tIRExpr(s->Ist.Exit.guard).simplify();
                        std::vector<Vns> guard_result;
                        if (guard.real()) {
                            if ((UChar)guard) {
                            Exit_guard_true:
                                if (s->Ist.Exit.jk != Ijk_Boring && s->Ist.Exit.jk != Ijk_Call && s->Ist.Exit.jk != Ijk_Ret)
                                {
                                    //ppIRSB(irsb);
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
                                    goto For_Begin;
                                }
                            }
                        }
                        else {
                            switch (eval_all(guard_result, solv, guard)) {
                            case 0: { status = Death; goto EXIT; }
                            case 1: {
                                if (((UChar)guard_result[0].simplify()) & 1) { goto Exit_guard_true; };
                                break;
                            }
                            case 2: {
                                branchChunks.emplace_back(BranchChunk(s->Ist.Exit.dst->Ico.U64, Vns(m_ctx, 0), guard, True));
                                if (!Ist_Exit_find_branch(branchChunks, guard, irsb, stmtn)) {
                                    ppIRSB(irsb);
                                    status = Death;
                                    vex_printf("not found!");
                                    goto EXIT;
                                };
                                status = Fork;
                                goto EXIT;
                            }
                            default: { vpanic("??"); }
                            }
                        }
                        break;
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
                    case Ist_AbiHint: //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
                        break; 
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
                            mem.Ist_Store(addr, ite(guard == 1, mem.Iex_Load(addr, (IRType)(data.bitn)), data));
                        }
                        break;
                    }
                    case Ist_MBE:  /*内存总线事件，fence/请求/释放总线锁*/
                    case Ist_LLSC:
                    default: {
                        vex_printf("what ppIRStmt %d\n", s->tag);
                        vpanic("what ppIRStmt");
                    }
                    }

                    traceIRStmtEnd(s);
                }

                switch (irsb->jumpkind) {
                case Ijk_Boring:        break;
                case Ijk_Call:          break;
                case Ijk_Ret:           break;
                case Ijk_SigTRAP: {
                SigTRAP:
                    if (get_hook(hs, guest_start)) {
                        setFlag(hs.cflag);
                        goto deal_bkp;
                    }
                    status = Death;
                    vex_printf("Ijk_SigTRAP: %p", guest_start);
                    goto EXIT;
                }
                default: {
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
                };
Isb_next:
                Vns next = tIRExpr(irsb->next).simplify();
                if (next.real()) {
                    guest_start = next;
                }
                else {
                    std::vector<Vns> result;
                    switch (eval_all(result, solv, next)) {
                    case 0: status = Death; goto EXIT;
                    case 1: {
                        guest_start = result[0].simplify();
                        break;
                    }
                    default: {
                        for (auto re : result) {
                            branchChunks.emplace_back(BranchChunk(re.simplify(), next, Vns(m_ctx, 0), True));
                        }
                        status = Fork;
                        goto EXIT;
                    }
                    };
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


    auto b = branchChunks.begin();
    auto e = branchChunks.end();
    while (b != e) {
        branch.emplace_back(b->getState(*this));
        b++;
    }
    thread_unregister();
    traceFinish();
    branchGo();
    return;

}

void State::branchGo()
{
    for(auto b : branch){
        State::pool->enqueue([b] {
            b->start(False);
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


bool State::Ist_Exit_find_branch(std::vector<BranchChunk>& branchChunks, Vns const& guard, IRSB* bb, UInt stmtn)
{
    //ppIRSB(bb);
    if (stmtn == bb->stmts_used - 1) {
        Vns next = tIRExpr(bb->next);
        if (next.real()) {
            branchChunks.emplace_back(BranchChunk((ADDR)next, Vns(m_ctx, 0), guard, False));
            return true;
        }
        else {
            return false;
        }
    }
    IRExpr* release = bb->next;
    for (UInt i = bb->stmts_used - 1; i >= 0; i--) {
        IRStmt* st = bb->stmts[i];
        switch (st->tag) {
        case Ist_Put: {
            if (release->tag == Iex_Get) {
                if (st->Ist.Put.offset == release->Iex.Get.offset) {
                    release = st->Ist.Put.data;
                }
            }
            break;
        }
        case Ist_WrTmp: {
            if (release->tag == Iex_RdTmp) {
                if (st->Ist.WrTmp.tmp == release->Iex.RdTmp.tmp) {
                    release = st->Ist.WrTmp.data;
                }
            }
            break;
        }
        case Ist_Store: {
            if (release->tag == Iex_Load) {
                if (st->Ist.Store.addr == release->Iex.Load.addr) {
                    release = st->Ist.Store.data;
                }
            }
            break;
        }
        default:
            return false;
        };
        if (release->tag == Iex_Const) {
            branchChunks.emplace_back(BranchChunk((ADDR)release->Iex.Const.con->Ico.U64, Vns(m_ctx, 0), guard, False));
            return true;;
        };
    }
    return false;
}



inline Bool State::treeCompress(z3::context& ctx, ADDR Target_Addr, State_Tag Target_Tag, std::vector<State_Tag>& avoid, ChangeView& change_view, std::hash_map<ULong, Vns>& change_map, std::hash_map<UShort, Vns>& regs_change_map) {
    ChangeView _change_view = { this, &change_view };
    if (branch.empty()) {
        for (auto av : avoid) {
            if (av == status) {
                return 2;
            }
        }
        if (guest_start == Target_Addr && status == Target_Tag) {
            ChangeView* _cv = &_change_view;
            do {
                auto state = _cv->elders;
                if (state->regs.record) {
                    for (auto offset : *state->regs.record) {
                        auto _Where = regs_change_map.lower_bound(offset);
                        if (_Where == regs_change_map.end()) {
                            regs_change_map[offset] = state->regs.Iex_Get(offset, Ity_I64, ctx);
                        }
                    }
                }
                for (auto mcm : state->mem.mem_change_map) {
                    vassert(mcm.second->record != NULL);
                    for (auto offset : *(mcm.second->record)) {
                        auto _Where = change_map.lower_bound(offset);
                        if (_Where == change_map.end()) {
                            auto Address = mcm.first + offset;
                            auto p = state->mem.getMemPage(Address);
                            vassert(p->user == state->mem.user);
                            change_map[Address] = p->unit->Iex_Get(offset, Ity_I64, ctx);
                        }
                    }
                }
                _cv = _cv->front;
            } while (_cv->front && _cv->front->elders);
            return False;
        }
        return True;
    }
    Bool has_branch = False;
    std::vector<State*> ::iterator it = branch.begin();
    while (it != branch.end()) {
        std::hash_map<ULong, Vns> _change_map;
        _change_map.reserve(20);
        std::hash_map<UShort, Vns> _regs_change_map;
        _change_map.reserve(20);
        Bool _has_branch = (*it)->treeCompress(ctx, Target_Addr, Target_Tag, avoid, _change_view, _change_map, _regs_change_map);
        if (!has_branch) {
            has_branch = _has_branch;
        }
        for (auto map_it : _change_map) {
            auto _Where = change_map.lower_bound(map_it.first);
            if (_Where == change_map.end()) {
                change_map[map_it.first] = map_it.second;
            }
            else {
                if (map_it.second.real() && (_Where->second.real()) && ((ULong)(map_it.second) == (ULong)(_Where->second))) {

                }
                else {
                    _Where->second = Vns(ctx, Z3_mk_ite(ctx, (*it)->getassert(ctx), map_it.second, _Where->second), 64);
                }
            }
        }
        for (auto map_it : _regs_change_map) {
            auto _Where = regs_change_map.lower_bound(map_it.first);
            if (_Where == regs_change_map.end()) {
                regs_change_map[map_it.first] = map_it.second;
            }
            else {
                if (((map_it.second.real()) && (_Where->second.real())) && ((ULong)(map_it.second) == (ULong)(_Where->second))) {

                }
                else {
                    _Where->second = Vns(ctx, Z3_mk_ite(ctx, (*it)->getassert(ctx), map_it.second, _Where->second), 64);
                }
            }
        }
        if (_has_branch == False) {
            delete* it;
            it = branch.erase(it);
            continue;
        }
        else if (_has_branch == 2) {
            delete* it;
            it = branch.erase(it);
            continue;
        }
        it++;
    }
    if (branch.empty() && status == Fork) {
        return 2;
    }
    else {
        return has_branch;
    }
}

void State::compress(ADDR Target_Addr, State_Tag Target_Tag, std::vector<State_Tag>& avoid)
{
    ChangeView change_view = { NULL, NULL };
    std::hash_map<ULong, Vns> change_map;
    change_map.reserve(20);
    std::hash_map<UShort, Vns> regs_change_map;
    regs_change_map.reserve(30);
    auto flag = treeCompress(m_ctx, Target_Addr, Target_Tag, avoid, change_view, change_map, regs_change_map);
    if (flag != True) {
        for (auto map_it : change_map) {
#ifdef  _DEBUG
            std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
            mem.Ist_Store(map_it.first, map_it.second);
        };
        for (auto map_it : regs_change_map) {
#ifdef  _DEBUG
            std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
            regs.Ist_Put(map_it.first, map_it.second);
        };
        guest_start = Target_Addr;
        branchChunks.clear();
        status = NewState;
    }
    else if (flag == True) {
        State* one_state = new State(this, Target_Addr);
        for (auto map_it : change_map) {
#ifdef  _DEBUG
            std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
            one_state->mem.Ist_Store(map_it.first, map_it.second.translate(*one_state));
        };

        for (auto map_it : regs_change_map) {
#ifdef  _DEBUG
            std::cout << std::hex << map_it.first << map_it.second << std::endl;
#endif //  _DEBUG
            one_state->regs.Ist_Put(map_it.first, map_it.second.translate(*one_state));
        };
        branch.emplace_back(one_state);
    }



}


State* BranchChunk::getState(State& fstate)
{
    State* ns = fstate.ForkState(m_oep);
    if (m_sym_addr.symbolic()) {
        ns->add_assert_eq(m_sym_addr.translate(ns->m_ctx), Vns(ns->m_ctx, m_oep));
    }
    if (m_guard.symbolic()) {
        ns->add_assert(m_guard.translate(ns->m_ctx), m_tof);
    }
    return ns;
}


#include "Unop.hpp"
#include "Binop.hpp"
#include "Triop.hpp"
#include "Qop.hpp"