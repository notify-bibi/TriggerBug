
#include "instopt/engine/vex_context.h"
#include "instopt/engine/memory.h"
#include "instopt/engine/state_base.h"
#include "instopt/helper/z3_target_call.h"
#include "instopt/engine/irsb_cache.h"


using namespace TR;

#ifdef _MSC_VER
#include<WIndows.h>
#include <sysinfoapi.h>



template<typename EaType, typename CountTy>
static rsval<CountTy> vex_read(StateBase& s, const rsval<EaType>& addr, const rsval<CountTy>& len) {
    UInt size = 0;
    if (len.real()) {
        size = len.tor();
    }
    else {
        spdlog::info("symbolic vex_read :ea{:s} len:{:s}", addr.str(), len.str());
        std::cin >> size;
    }

    std::string st;
    char buff[2];
    buff[1] = 0;
    UInt n;
    for (n = 0; n < size && buff[0] != '\n'; n += 1) {
        buff[0] = getchar();
        s.mem.store(addr + n, buff[0]);
        st.append(buff);
    }
    spdlog::info("vex_read :ea{:s} len:{:s} get:{:d} [{:s}]", addr.str(), len.str(), size, st);
    s.logger->info("vex_read :ea{:s} len:{:s} get:{:d} [{:s}]", addr.str(), len.str(), size, st);
    return rsval<EaType>(s.ctx(), n);
    
}

template<typename EaType, typename CountTy>
static void vex_write(StateBase& s, const rsval<EaType>& addr, const rsval<CountTy>& len) {
    UInt size = 0;
    if (len.real()) {
        size = len.tor();
    }else {
        s.logger->warn("symbolic vex_write : ea:{:s} len:{:s}", addr.str(), len.str());
        std::cin >> size;
    }
    std::string st;
    char buff[2];
    buff[1] = 0;
    for (UInt n = 0; n < size; n += 1) {
        auto chr = s.mem.template load<Ity_I8>(addr + n);
        if (chr.real()) {
            buff[0] = chr.tor();
            st.append(buff);
        }
        else {
            st.append(chr.str());
        }
    }
    spdlog::info("vex_write : ea:{:s} len:{:s} put:{:d} [{:s}]", addr.str(), len.str(), size, st);
    s.logger->info("vex_write : ea:{:s} len:{:s} put:{:d} [{:s}]", addr.str(), len.str(), size, st);
   
}



rsval<Long> io_vex_read(StateBase& s, const rsval<ULong>& addr, const rsval<Long>& len)
{
    return vex_read<ULong, Long>(s, addr, len);
}

void io_vex_write(StateBase& s, const rsval<ULong>& addr, const rsval<Long>& len) {

    vex_write<ULong, Long>(s, addr, len);
}



UInt vex_info::gMaxThreadsNum() {
    SYSTEM_INFO SysInfo;
    GetSystemInfo(&SysInfo);
    return SysInfo.dwNumberOfProcessors;
}
#elif defined(LINUX) || defined(SOLARIS) || defined(AIX)
#include <sys/sysinfo.h>
UInt vex_info::gMaxThreadsNum() {
    return get_nprocs();   //GNU fuction 
}
#else
UInt vex_info::gMaxThreadsNum() {
    return 8;   //
}
#warning  gMaxThreadsNum ret 8
#endif

__attribute__((noreturn))
static void failure_exit() {
    throw Expt::IRfailureExit("valgrind error exit");
}

//typedef void (*logger_function)(const HChar* bytes, SizeT nbytes);



static void _vex_log_bytes(const HChar* bytes, SizeT nbytes) {
    std::cout << bytes;
    //throw Expt::IRfailureExit(bytes);
}


clock_t tr_begin_run = clock();
static bool is_LibVEX_Init = false;
VexControl vex_info::init_VexControl() {
    VexControl vc;
    LibVEX_default_VexControl(&vc);
    vc.iropt_verbosity = 0;
    vc.iropt_level = giropt_level();
    #warning "what is iropt_unroll_thresh"
    vc.iropt_unroll_thresh = 0;
    vc.guest_max_insns = gmax_insns();
    // vc.guest_chase_thresh = 0;   
#if 1
    vc.guest_chase = false; //²»Ðí×·¸Ï
#else
    vc.guest_chase = true; // chain
#endif
    vc.iropt_register_updates_default = gRegisterUpdates();


    if (!is_LibVEX_Init) {
        tr_begin_run = clock();
        Func_Map_Init();
        is_LibVEX_Init = true;
    }
    LibVEX_Init(&failure_exit, &_vex_log_bytes, 0/*debuglevel*/, &vc);
    return vc;
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

Bool vex_info::gis_mode_32(VexArch guest)
{
    IRConst c;
    switch (guest) {
    case VexArchX86: 
    case VexArchARM:
    case VexArchS390X:
    case VexArchMIPS32:
    case VexArchPPC32: return true;
    case VexArchPPC64:
    case VexArchAMD64:
    case VexArchMIPS64:
    case VexArchARM64: return false;
    default:
        vassert(0);
    }
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
     //return fastMask(guest_extents->n_used);
     return 0;
 }

 static void* dispatch(void) {
     std::cout << "dispatch\n" << std::endl;
     return NULL;
 }

 //static IRSB* finaltidy (IRSB* bb) {
 //
 //
 //}

 //static IRSB* instrument1( /*callback_opaque*/void*,
 //    IRSB*,
 //    const VexGuestLayout*,
 //    const VexGuestExtents*,
 //    const VexArchInfo*,
 //    IRType gWordTy, IRType hWordTy) {
 //
 //}


 //static IRSB* instrument2( /*callback_opaque*/void*,
 //    IRSB*,
 //    const VexGuestLayout*,
 //    const VexGuestExtents*,
 //    const VexArchInfo*,
 //    IRType gWordTy, IRType hWordTy) {

 //}

 Bool chase_into_ok(void* value, Addr addr) {
     //std::cout << value << addr << std::endl;
     return true;
 }

 namespace TR {


     vex_info::vex_info(VexArch guest, Int iropt_level, UInt guest_max_insns, VexRegisterUpdates iropt_register_updates_default, ULong traceflags, UInt maxThreadsNum) :
         m_guest(guest),
         m_iropt_level(iropt_level),
         m_guest_max_insns(guest_max_insns), //not limit size
         m_iropt_register_updates_default(iropt_register_updates_default),
         m_traceflags(traceflags),
         m_maxThreadsNum(maxThreadsNum),
         m_bpt_code(gsoftwareBpt(guest)),
         m_IRoffset_IP(vex_info::gRegsIpOffset(guest)), m_IRoffset_SP(vex_info::gRegsSPOffset(guest)), m_IRoffset_BP(vex_info::gRegsBPOffset(guest)),
         m_mode_32(gis_mode_32(guest))
     {
     }
     vex_info::vex_info(VexArch guest) 
         :vex_info(guest, 2, 0x200, VexRegUpdSpAtMemAccess, 0, gMaxThreadsNum())
     {}

     vex_info::vex_info(const vex_info& v) :
         m_guest(v.m_guest),
         m_iropt_level(v.m_iropt_level),
         m_guest_max_insns(v.m_guest_max_insns), //not limit size
         m_iropt_register_updates_default(v.m_iropt_register_updates_default),
         m_traceflags(v.m_traceflags),
         m_maxThreadsNum(v.m_maxThreadsNum),
         m_bpt_code(v.m_bpt_code),
         m_IRoffset_IP(v.m_IRoffset_IP), m_IRoffset_SP(v.m_IRoffset_SP), m_IRoffset_BP(v.m_IRoffset_BP),
         m_mode_32(v.m_mode_32)
     {

     }

     void vex_info::operator=(const vex_info& guest)
     {
         this->~vex_info();
         new(this) vex_info(guest);
     }

     vex_info::~vex_info()
     {
     }

     VexArch vex_info::enable_long_mode()
     {
         vassert(m_mode_32);
         m_mode_32 = false;
         VexArch guest = VexArch_INVALID;
         switch (m_guest) {
         case VexArchX86: guest = VexArchAMD64; break;
         case VexArchARM: guest = VexArchARM64; break;
         case VexArchMIPS32: guest = VexArchMIPS64; break;
         case VexArchPPC32:  guest = VexArchPPC64; break;
         default:
             VPANIC("don't support");
         }
         // add diff
         this->~vex_info();
         new(this) vex_info(guest, m_iropt_level, m_guest_max_insns, m_iropt_register_updates_default, m_traceflags, m_maxThreadsNum);
         
         return guest;
     }

     VexArch vex_info::disable_long_mode()
     {
         vassert(!m_mode_32);
         m_mode_32 = true;
         VexArch guest = VexArch_INVALID;
         switch (m_guest) {
         case VexArchAMD64: guest = VexArchX86; break;
         case VexArchARM64: guest = VexArchARM; break;
         case VexArchMIPS64: guest = VexArchMIPS32; break;
         case VexArchPPC64:  guest = VexArchPPC32; break;
         default:
             VPANIC("don't support");
         }
         // add diff
         this->~vex_info();
         new(this) vex_info(guest, m_iropt_level, m_guest_max_insns, m_iropt_register_updates_default, m_traceflags, m_maxThreadsNum);

         return guest;
     }





     vctx_base::vctx_base(Int max_threads) 
         : m_top_state(nullptr),
         m_pool(gMaxThreadsNum(max_threads)), 
         m_user_counter(1)
     {
     }

     UInt vctx_base::gMaxThreadsNum(Int max_threads)
     {
         Int max = vex_info::gMaxThreadsNum();
         if (max_threads > 0) {
             if (max_threads < max * 2) {
                 return max_threads;
             }
         }
         return (UInt)max;
     }

 };




 namespace TR{
    void vex_context::hook_add(HWord addr, Hook_CallBack func, TRControlFlags cflag)
    {
        if (m_callBackDict.find(addr) == m_callBackDict.end()) {
            m_callBackDict[addr] = Hook_struct{ func , cflag };
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

    
    bool vex_context::get_hook(Hook_struct& hs, HWord ea)
    {
        auto _where = m_callBackDict.find(ea);
        if (_where == m_callBackDict.end()) {
            return false;
        }
        hs = _where->second;
        return true;
    }

    
    vex_context::vex_context(Int max_threads)
        :vctx_base(max_threads)
    {

        m_irsb_cache = new_IRSBCache();
        
        constructer();
    };

    void vex_context::constructer()
    {
            hook_read(io_vex_read);
            hook_write(io_vex_write);
    }

    vex_context::~vex_context()
    {
        pool().wait(); // haha
        del_IRSBCache(m_irsb_cache);
        m_irsb_cache = nullptr;
    }

    void vex_context::hook_del(HWord addr)
    {
        if (m_callBackDict.find(addr) != m_callBackDict.end()) {
            //pool->wait();
            HASH_MAP<Addr64, Hook_struct>::iterator h = m_callBackDict.find(addr);
            // i dont want break irsb
            // m_top_state->mem.Ist_Store(addr, tval(m_top_state->ctx(), h->second.original, h->second.nbytes)); 
            m_callBackDict.erase(h);
        }
    }

    z3::expr vex_context::idx2value(TR::StateBase& state, HWord base, Z3_ast index)
    {
        HASH_MAP<Addr64, Hook_idx2Value>::iterator _where = m_tableIdxDict.find(base);
        return (_where != m_tableIdxDict.end()) ? _where->second(state, base, index) : z3::expr(state);
    }


    static VexEndness running_endness(void)
    {
#if __BYTE_ORDER == __LITTLE_ENDIAN
        return VexEndnessLE;
#elif __BYTE_ORDER == __BIG_ENDIAN
        return VexEndnessBE;
#else
        fprintf(stderr, "cannot determine endianness\n");
        exit(1);
#endif
    }

    static VexEndness arch_endness(VexArch va) {
        switch (va) {
        case VexArch_INVALID: vassert(0);
        case VexArchX86:    return VexEndnessLE;
        case VexArchAMD64:  return VexEndnessLE;
        case VexArchARM:    return VexEndnessLE;
        case VexArchARM64:  return VexEndnessLE;
        case VexArchPPC32:  return VexEndnessBE;
        case VexArchPPC64:
            /* ppc64 supports BE or LE at run time. So, on a LE system,
               returns LE, on a BE system, return BE. */
            return running_endness();
        case VexArchS390X:  return VexEndnessBE;
        case VexArchMIPS32:
        case VexArchMIPS64:
            /* mips32/64 supports BE or LE, but at compile time.
               If mips64 is compiled on a non mips system, the VEX lib
               is missing bit and pieces of code related to endianness.
               The mandatory code for this test is then compiled as BE.
               So, if this test runs on a mips system, returns the
               running endianness. Otherwise, returns BE as this one
               has the more chances to work. */
        {
        }
        default: vassert(0);
        }
    }
    /* returns whatever kind of hwcaps needed to make
   the host and/or guest VexArch happy. */
    /*static UInt arch_hwcaps(VexArch va) {
        switch (va) {
        case VexArch_INVALID: vassert(0);
        case VexArchX86:    return 0;
        case VexArchAMD64:  return 0;
        case VexArchARM:    return 7;
        case VexArchARM64:  return 0;
        case VexArchPPC32:  return 0;
        case VexArchPPC64:  return 0;
        case VexArchS390X:  return VEX_HWCAPS_S390X_LDISP;
#if (__mips_isa_rev>=6)
        case VexArchMIPS32: return VEX_PRID_COMP_MIPS | VEX_MIPS_CPU_ISA_M32R6 |
            VEX_MIPS_HOST_FR;
        case VexArchMIPS64: return VEX_PRID_COMP_MIPS | VEX_MIPS_CPU_ISA_M64R6 |
            VEX_MIPS_HOST_FR;
#else
        case VexArchMIPS32: return VEX_PRID_COMP_MIPS;
        case VexArchMIPS64: return VEX_PRID_COMP_MIPS | VEX_MIPS_HOST_FR;
#endif
        default: vassert(0);
        }
    }*/

    void vex_info::init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk, VexArch guest_arch, ULong traceflags) {
        //HOSTARCH
        VexArch host_arch = guest_arch;
        /*vai_host vai_guest*/
        VexEndness guest_endness = arch_endness(guest_arch);
        VexEndness host_endness = arch_endness(host_arch);

        memset(&vta_chunk, 0, sizeof(vta_chunk));
        LibVEX_default_VexArchInfo(&vta_chunk.archinfo_guest);
        LibVEX_default_VexArchInfo(&vta_chunk.archinfo_host);

        vex_hwcaps_vai(guest_arch, &vta_chunk.archinfo_guest);
        vex_hwcaps_vai(host_arch, &vta_chunk.archinfo_host);


        /*vbi*/
        LibVEX_default_VexAbiInfo(&vta_chunk.abiinfo_both);
        vta_chunk.abiinfo_both.guest_amd64_assume_gs_is_const = true;
        vta_chunk.abiinfo_both.guest_amd64_assume_fs_is_const = true;

        // Use some values that makes ARM64 happy.
        vta_chunk.archinfo_guest.arm64_dMinLine_lg2_szB = 6;
        vta_chunk.archinfo_guest.arm64_iMinLine_lg2_szB = 6;

        // Use some values that makes AMD64 happy.
        vta_chunk.abiinfo_both.guest_stack_redzone_size = 128;
        vex_prepare_vbi(guest_arch, &vta_chunk.abiinfo_both);

        vta_chunk.callback_opaque = NULL;
        vta_chunk.preamble_function = NULL;
        vta_chunk.instrument1 = NULL;
        vta_chunk.instrument2 = NULL;
        vta_chunk.finaltidy = NULL;
        vta_chunk.preamble_function = NULL; // first   [Bool    (*preamble_function)(/*callback_opaque*/void*, IRSB*);]

        vta_chunk.disp_cp_chain_me_to_slowEP = (void*)dispatch;
        vta_chunk.disp_cp_chain_me_to_fastEP = (void*)dispatch;
        vta_chunk.disp_cp_xindir = (void*)dispatch;
        vta_chunk.disp_cp_xassisted = (void*)dispatch;

        vta_chunk.arch_guest = guest_arch;
        vta_chunk.archinfo_guest.endness = guest_endness;
        //vta_chunk.archinfo_guest.hwcaps = arch_hwcaps(vta_chunk.arch_guest);
        vta_chunk.arch_host = guest_arch;
        vta_chunk.archinfo_host.endness = guest_endness;
        //vta_chunk.archinfo_host.hwcaps = arch_hwcaps(vta_chunk.arch_host);

        memset(&vge_chunk, 0 , sizeof(vge_chunk));
        vta_chunk.guest_extents = &vge_chunk;
        vta_chunk.chase_into_ok = chase_into_ok;
        vta_chunk.needs_self_check = needs_self_check;
        vta_chunk.traceflags = traceflags;

#ifdef VEX_BACKEND_FN
        vta_chunk.host_bytes_size = 0x2000;
        vta_chunk.host_bytes = new UChar[0x2000];
        vta_chunk.host_bytes_used = new Int;
#endif
    }

};
