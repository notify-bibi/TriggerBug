#include "engine/vex_context.h"
#include "engine/variable.h"
#include "engine/memory.h"

using namespace TR;

UInt vex_info::gMaxThreadsNum() {
    SYSTEM_INFO SysInfo;
    GetSystemInfo(&SysInfo);
    return SysInfo.dwNumberOfProcessors;
}


 IRConst vex_info::gsoftwareBpt(VexArch guest)
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

 Int vex_info::gRegsIpOffset(VexArch guest) {
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
        return -1;
    }
}

 Int vex_info::gRegsSPOffset(VexArch arch) {
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
         std::cout << "Invalid arch in vex_prepare_vai.\n" << std::endl;
         return -1;
     }
 }

 Int vex_info::gRegsBPOffset(VexArch arch) {
     switch (arch) {
     case VexArchX86:return offsetof(VexGuestX86State, guest_EBP);
     case VexArchAMD64:return offsetof(VexGuestAMD64State, guest_RBP);
     case VexArchARM:return offsetof(VexGuestARMState, guest_R11);
     case VexArchARM64:return offsetof(VexGuestARM64State, guest_XSP);
     case VexArchPPC32:return offsetof(VexGuestPPC32State, guest_GPR1);
     case VexArchPPC64:return offsetof(VexGuestPPC64State, guest_GPR1);
     case VexArchS390X:return offsetof(VexGuestS390XState, guest_r15);
     case VexArchMIPS32:return offsetof(VexGuestMIPS32State, guest_r29);
     case VexArchMIPS64:return offsetof(VexGuestPPC64State, guest_GPR1);
     default:
         std::cout << "Invalid arch in vex_prepare_vai.\n" << std::endl;
         return -1;
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

namespace TR {
    template<typename ADDR>
    inline void vex_context<ADDR>::hook_add(IN State<ADDR>& state, ADDR addr, State_Tag(*_func)(State<ADDR>&), TRControlFlags cflag)
    {
        Hook_CB func = (Hook_CB) _func;
        if (m_callBackDict.find(addr) == m_callBackDict.end()) {
            Vns o = state.mem.Iex_Load<Ity_I64>(addr);
            vassert(o.real());
            m_callBackDict[addr] = Hook_struct{ func , IRConstTag2nb(state.info().softwareBptConst()->tag) , o , cflag };
            state.mem.Ist_Store_bpt(addr, Vns(state.m_ctx, state.info().softwareBptConst()));
        }
        else {
            if (func) {
                m_callBackDict[addr].cb = func;
            }
            if (cflag != CF_None) {
                m_callBackDict[addr].cflag = cflag;
            }
        }
    }

    template<typename ADDR>
    bool vex_context<ADDR>::get_hook(Hook_struct& hs, ADDR addr)
    {
        auto _where = m_callBackDict.find(addr);
        if (_where == m_callBackDict.end()) {
            return false;
        }
        hs = _where->second;
        return true;
    }

    template<typename ADDR>
    void vex_context<ADDR>::hook_del(ADDR addr)
    {
        if (m_callBackDict.find(addr) != m_callBackDict.end()) {
            //pool->wait();
            std::hash_map<Addr64, Hook_struct>::iterator h = m_callBackDict.find(addr);
            m_top_state->mem.Ist_Store_bpt(addr, Vns(m_top_state->m_ctx, h->second.original, h->second.nbytes));
            m_callBackDict.erase(h);
        }
    }

    template<typename ADDR>
    z3::expr vex_context<ADDR>::idx2value(const TR::State<ADDR>& state, Addr64 base, Z3_ast index)
    {
        auto _where = m_tableIdxDict.find(base);
        z3::expr (*CB) (const State<ADDR>&, Addr64 /*base*/, Z3_ast /*idx*/) = (z3::expr(*) (const State<ADDR>&, Addr64 /*base*/, Z3_ast /*idx*/))_where->second;
        return (_where != m_tableIdxDict.end()) ? CB(state, (Addr64)base, (Z3_ast)index) : z3::expr(state);
    }


    vex_info::vex_info(VexArch guest, const char* filename) :
        m_bin(filename),
        m_guest(guest),
        m_iropt_level(2),
        m_guest_max_insns(100),
        m_iropt_register_updates_default(VexRegUpdSpAtMemAccess),
        m_guest_system(TR::unknowSystem),
        m_traceflags(0),
        m_maxThreadsNum(gMaxThreadsNum()),
        m_bpt_code(gsoftwareBpt(guest)),
        m_IRoffset_IP(vex_info::gRegsIpOffset(guest)), m_IRoffset_SP(vex_info::gRegsSPOffset(guest)), m_IRoffset_BP(vex_info::gRegsBPOffset(guest))
    {
    }



    void vex_info::init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk, VexArch guest, ULong traceflags) {
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


};

template TR::ctx32;
template TR::ctx64;
