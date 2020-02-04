#include "Kernel.hpp"
#include "State_class.hpp"

tinyxml2::XMLDocument               Vex_Info::doc = tinyxml2::XMLDocument();
VexRegisterUpdates                  Vex_Info::iropt_register_updates_default = VexRegUpdSpAtMemAccess;
Int                                 Vex_Info::iropt_level = 2;
UInt                                Vex_Info::guest_max_insns = 100;
tinyxml2::XMLError                  Vex_Info::err = tinyxml2::XML_ERROR_COUNT;
tinyxml2::XMLElement* Vex_Info::doc_TriggerBug = nullptr;
tinyxml2::XMLElement* Vex_Info::doc_VexControl = nullptr;
tinyxml2::XMLElement* Vex_Info::doc_debug = nullptr;
GuestSystem                         Vex_Info::guest_system = unknowSystem;
VexArch                             Vex_Info::guest = VexArch_INVALID;
const char* Vex_Info::MemoryDumpPath = "你没有这个文件";
UInt                                Vex_Info::MaxThreadsNum = 16;
Int                                 Vex_Info::traceflags = 0;


UInt Vex_Info::_gtraceflags() {
    tinyxml2::XMLElement* _traceflags = doc_VexControl->FirstChildElement("traceflags");
    if (_traceflags) return _traceflags->IntText();
    return 0;
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

UInt Vex_Info::gRegsIpOffset() {
    switch (guest) {
    case VexArchX86:return X86_IR_OFFSET::eip;
    case VexArchAMD64:return AMD64_IR_OFFSET::rip;
    case VexArchARM:
    case VexArchARM64:
    case VexArchPPC32:
    case VexArchPPC64:
    case VexArchS390X:
    case VexArchMIPS32:
    case VexArchMIPS64:
    default:
        std::cout << "Invalid arch in vex_prepare_vai.\n" << std::endl;
        vassert(0);
    }
}

void Vex_Info::vex_info_init(const char* filename)
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

    if (doc_VexControl) {
        _giropt_register_updates_default();
        _giropt_level();
        _gguest_max_insns();
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


bool Vex_Info::is_mode_64() {
    switch (guest) {
    case VexArchS390X:
    case VexArchARM64:
    case VexArchPPC64:
    case VexArchMIPS64:
    case VexArchAMD64:return true;
    case VexArchPPC32:
    case VexArchARM:
    case VexArchMIPS32:
    case VexArchX86:return false;
    default:
        VPANIC("Invalid arch\n"); return false;
    }
}

Z3_ast Kernel::idx2Value(Addr64 base, Z3_ast idx)
{
    auto _where = TableIdxDict.lower_bound(base);
    if (_where != TableIdxDict.end()) {
        //vex_printf("pycfun: %p \n", _where->second);
        return _where->second(this, (Addr64)base, (Z3_ast)idx);
    }
    else
    {
        return (Z3_ast)NULL;
    }
}

Addr64 Kernel::get_cpu_ip()
{
    if (is_mode_64()) {
        return (operator State<Addr64> & ()).get_cpu_ip();
    }
    else {
        return (operator State<Addr32> & ()).get_cpu_ip();
    }
}
Kernel::operator TRsolver& ()
{
    if (is_mode_64()) {
        return operator State<Addr64> & ().solv;
    }
    else {
        return operator State<Addr32> & ().solv;
    }
}



#include "Unop.hpp"
#include "Binop.hpp"
#include "Triop.hpp"
#include "Qop.hpp"
