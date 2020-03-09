#include "Kernel.hpp"
#include "State_class.hpp"


void Vex_Info::_gtraceflags() {
    tinyxml2::XMLElement* _traceflags = doc_VexControl->FirstChildElement("traceflags");
    if (_traceflags) traceflags = _traceflags->IntText();
}

tinyxml2::XMLError Vex_Info::loadFile(const char* filename) {
    tinyxml2::XMLError error = doc.LoadFile(filename);
    if (error != tinyxml2::XML_SUCCESS) {
        printf("error: %d Error filename %s    at:%s line %d", error, filename, __FILE__, __LINE__);
        exit(1);
    }
    return error;
}

void Vex_Info::_gGuestArch() {
    auto _VexArch = doc_TriggerBug->FirstChildElement("VexArch");
    if (_VexArch) sscanf(_VexArch->GetText(), "%x", &guest);
}

void Vex_Info::_gMemoryDumpPath() {
    tinyxml2::XMLElement* _MemoryDumpPath = doc_TriggerBug->FirstChildElement("MemoryDumpPath");
    if (_MemoryDumpPath) MemoryDumpPath = _MemoryDumpPath->GetText();
}

void Vex_Info::_gVexArchSystem() {
    tinyxml2::XMLElement* _VexArchSystem = doc_TriggerBug->FirstChildElement("VexArchSystem");
    if (_VexArchSystem) {

        if (!strcmp(_VexArchSystem->GetText(), "linux")) {
            guest_system = linux;
        }
        if (!strcmp(_VexArchSystem->GetText(), "windows")) {
            guest_system = windows;
        }
        if (!strcmp(_VexArchSystem->GetText(), "win")) {
            guest_system = windows;
        }
    }
}

void Vex_Info::_giropt_register_updates_default() {
    tinyxml2::XMLElement* _iropt_register_updates_default = doc_VexControl->FirstChildElement("iropt_register_updates_default");
    if (_iropt_register_updates_default) sscanf(_iropt_register_updates_default->GetText(), "%x", &iropt_register_updates_default);
}

void Vex_Info::_giropt_level() {
    tinyxml2::XMLElement* _iropt_level = doc_VexControl->FirstChildElement("iropt_level");
    if (_iropt_level) iropt_level = _iropt_level->IntText();
}

void Vex_Info::_gguest_max_insns() {
    auto _guest_max_insns = doc_TriggerBug->FirstChildElement("guest_max_insns");
    if (_guest_max_insns) guest_max_insns = _guest_max_insns->IntText();
}

void Vex_Info::_gMaxThreadsNum() {
    UInt    mMaxThreadsNum = 16;
    tinyxml2::XMLElement* _MaxThreadsNum = doc_TriggerBug->FirstChildElement("MaxThreadsNum");
    if (_MaxThreadsNum) _MaxThreadsNum->QueryIntText((Int*)(&mMaxThreadsNum));
    MaxThreadsNum = mMaxThreadsNum;
}

UInt Vex_Info::gRegsIpOffset() const {
    switch (guest) {
    case VexArchX86:return X86_IR_OFFSET::EIP;
    case VexArchAMD64:return AMD64_IR_OFFSET::RIP;
    case VexArchARM:return ARM_IR_OFFSET::R15T;
    case VexArchARM64:return ARM64_IR_OFFSET::PC;
    case VexArchPPC32:return PPC32_IR_OFFSET::CIA;
    case VexArchPPC64:return PPC64_IR_OFFSET::CIA;
    case VexArchS390X:return S390X_IR_OFFSET::IA;
    case VexArchMIPS32:return MIPS32_IR_OFFSET::PC;
    case VexArchMIPS64:return MIPS64_IR_OFFSET::PC;
    default:
        std::cout << "Invalid arch in vex_prepare_vai.\n" << std::endl;
        vassert(0);
    }
}

IRConst Vex_Info::_softwareBpt()
{
    IRConst c;
    switch (guest) {
    case VexArchX86:
    case VexArchAMD64:  c.Ico.U8 = 0xcc; c.tag = Ico_U8; break;
    case VexArchARM:    
    case VexArchARM64:
    case VexArchPPC32:
    case VexArchPPC64:
    case VexArchS390X:
    case VexArchMIPS32:
    case VexArchMIPS64:
    default:
        vassert(0);
    }
    return c;
}


void Vex_Info::_vex_info_init(const char* filename)
{
    iropt_register_updates_default = VexRegUpdSpAtMemAccess;
    iropt_level = 2;
    guest_max_insns = 100;
    err = loadFile(filename);
    doc_TriggerBug = doc.FirstChildElement("TriggerBug");
    doc_VexControl = doc_TriggerBug->FirstChildElement("VexControl");
    doc_debug = doc_TriggerBug->FirstChildElement("DEBUG");

    guest_system = unknowSystem;
    guest = VexArch_INVALID;
    MemoryDumpPath = "file not found!!! ";

    _gGuestArch();
    _gVexArchSystem();
    _gMemoryDumpPath();
    _gMaxThreadsNum();
    _gguest_max_insns();

    if (doc_VexControl) {
        _giropt_register_updates_default();
        _giropt_level();
        _gtraceflags();
    }
    trtraceflags = 0;
    if (doc_debug) {
        bool traceState = false, traceJmp = false, ppStmts = false, TraceSymbolic = false;
        auto _ppStmts = doc_debug->FirstChildElement("ppStmts");
        auto _TraceState = doc_debug->FirstChildElement("TraceState");
        auto _TraceJmp = doc_debug->FirstChildElement("TraceJmp");
        auto _TraceSymbolic = doc_debug->FirstChildElement("TraceSymbolic");

        if (_TraceState) _TraceState->QueryBoolText(&traceState);
        if (_TraceJmp) _TraceJmp->QueryBoolText(&traceJmp);
        if (_ppStmts) _ppStmts->QueryBoolText(&ppStmts);
        if (_TraceSymbolic) _TraceSymbolic->QueryBoolText(&TraceSymbolic);
        if (traceState) trtraceflags |= CF_traceState;
        if (traceJmp) trtraceflags |= CF_traceJmp;
        if (ppStmts) trtraceflags |= CF_ppStmts;
        if (TraceSymbolic) trtraceflags |= CF_TraceSymbolic;
    }
    
}



static void vex_hwcaps_vai(VexArch arch, VexArchInfo* vai) {
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

static void vex_prepare_vbi(VexArch arch, VexAbiInfo* vbi) {
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


static UInt needs_self_check(void* callback_opaque, VexRegisterUpdates* pxControl, const VexGuestExtents* guest_extents) {
    //std::cout << "needs_self_check\n" << std::endl;
    return 0;
}

static void* dispatch(void) {
    std::cout << "dispatch\n" << std::endl;
    return NULL;
}

Bool chase_into_ok(void* value, Addr addr) {
    std::cout << value << addr << std::endl;
    return True;
}


void Vex_Info::init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk, VexArch guest, Int traceflags) {
    VexArchInfo vai_guest;
    VexArchInfo vai_host;
    VexAbiInfo vbi;

    /*vai_host vai_guest*/
    LibVEX_default_VexArchInfo(&vai_host);
    LibVEX_default_VexArchInfo(&vai_guest);
    vex_hwcaps_vai(HOSTARCH, &vai_host);
    vex_hwcaps_vai(guest, &vai_guest);
    vai_host.endness = VexEndnessLE;//VexEndnessBE
    vai_guest.endness = VexEndnessLE;//VexEndnessBE

    /*vbi*/
    LibVEX_default_VexAbiInfo(&vbi);
    vbi.guest_amd64_assume_gs_is_const = True;
    vbi.guest_amd64_assume_fs_is_const = True;
    vex_prepare_vbi(guest, &vbi);

    vta_chunk.callback_opaque = NULL;
    vta_chunk.preamble_function = NULL;
    vta_chunk.instrument1 = NULL;
    vta_chunk.instrument2 = NULL;
    vta_chunk.finaltidy = NULL;
    vta_chunk.preamble_function = NULL;

    vta_chunk.disp_cp_chain_me_to_slowEP = (void*)dispatch;
    vta_chunk.disp_cp_chain_me_to_fastEP = (void*)dispatch;
    vta_chunk.disp_cp_xindir = (void*)dispatch;
    vta_chunk.disp_cp_xassisted = (void*)dispatch;

    vta_chunk.abiinfo_both = vbi;
    vta_chunk.archinfo_guest = vai_guest;
    vta_chunk.archinfo_host = vai_host;
    vta_chunk.arch_guest = guest;
    vta_chunk.arch_host = HOSTARCH;
    vta_chunk.guest_extents = &vge_chunk;
    vta_chunk.chase_into_ok = chase_into_ok;
    vta_chunk.needs_self_check = needs_self_check;
    vta_chunk.traceflags = traceflags;
}



z3::sort translateRM(z3::context& m_ctx, IRRoundingMode md) {
    switch (md)
    {
    case Irrm_NEAREST: {return z3::sort(m_ctx, Z3_mk_fpa_rne(m_ctx)); }
    case Irrm_PosINF: {return z3::sort(m_ctx, Z3_mk_fpa_rtp(m_ctx)); }
    case Irrm_ZERO: {return z3::sort(m_ctx, Z3_mk_fpa_rtz(m_ctx)); }
    case Irrm_NEAREST_TIE_AWAY_0: {return z3::sort(m_ctx, Z3_mk_fpa_rna(m_ctx)); }
    default:
        vassert(md == Irrm_NegINF);
        return z3::sort(m_ctx, Z3_mk_fpa_rtn(m_ctx));
    }
}


#include "Unop.hpp"
#include "Binop.hpp"
#include "Triop.hpp"
#include "Qop.hpp"
