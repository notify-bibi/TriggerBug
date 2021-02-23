
#ifdef VEX_BACKEND_FN

#include "main_globals.h"
#include "main_util.h"
#include "host_generic_regs.h"
#include "ir_opt.h"

#include "host_x86_defs.h"
#include "host_amd64_defs.h"
#include "host_ppc_defs.h"
#include "host_arm_defs.h"
#include "host_arm64_defs.h"
#include "host_s390_defs.h"
#include "host_mips_defs.h"
#include "host_nanomips_defs.h"

#include "guest_generic_bb_to_IR.h"
#include "guest_x86_defs.h"
#include "guest_amd64_defs.h"
#include "guest_arm_defs.h"
#include "guest_arm64_defs.h"
#include "guest_ppc_defs.h"
#include "guest_s390_defs.h"
#include "guest_mips_defs.h"
#include "guest_nanomips_defs.h"

#include "host_generic_simd128.h"
#include <libvex_guest_mips64.h>
#include <libvex_guest_mips32.h>
#include <libvex_guest_arm64.h>
#include <libvex_guest_arm.h>


#define X86FN(f) f
#define X86ST(f) f


#define AMD64FN(f) f
#define AMD64ST(f) f

#if defined(VGA_ppc32) || defined(VEXMULTIARCH)
#define PPC32FN(f) f
#define PPC32ST(f) f
#else
#define PPC32FN(f) NULL
#define PPC32ST(f) vassert(0)
#endif

#if defined(VGA_ppc64be) || defined(VGA_ppc64le) || defined(VEXMULTIARCH)
#define PPC64FN(f) f
#define PPC64ST(f) f
#else
#define PPC64FN(f) NULL
#define PPC64ST(f) vassert(0)
#endif

#if defined(VGA_s390x) || defined(VEXMULTIARCH)
#define S390FN(f) f
#define S390ST(f) f
#else
#define S390FN(f) NULL
#define S390ST(f) vassert(0)
#endif

#if defined(VGA_arm) || defined(VEXMULTIARCH)
#define ARMFN(f) f
#define ARMST(f) f
#else
#define ARMFN(f) NULL
#define ARMST(f) vassert(0)
#endif

#if defined(VGA_arm64) || defined(VEXMULTIARCH)
#define ARM64FN(f) f
#define ARM64ST(f) f
#else
#define ARM64FN(f) NULL
#define ARM64ST(f) vassert(0)
#endif

#if defined(VGA_mips32) || defined(VEXMULTIARCH)
#define MIPS32FN(f) f
#define MIPS32ST(f) f
#else
#define MIPS32FN(f) NULL
#define MIPS32ST(f) vassert(0)
#endif

#if defined(VGA_mips64) || defined(VEXMULTIARCH)
#define MIPS64FN(f) f
#define MIPS64ST(f) f
#else
#define MIPS64FN(f) NULL
#define MIPS64ST(f) vassert(0)
#endif

#if defined(VGA_nanomips) || defined(VEXMULTIARCH)
#define NANOMIPSFN(f) f
#define NANOMIPSST(f) f
#else
#define NANOMIPSFN(f) NULL
#define NANOMIPSST(f) vassert(0)
#endif



/* debug paranoia level */
extern Int* get_vex_debuglevel();

/* trace flags */
extern Int* get_vex_traceflags();

/* Max # guest insns per bb */
extern VexControl* get_vex_control();

/* trace flags */
Int vex_traceflags = 0xff;

/* Max # guest insns per bb */
#define vex_control (*get_vex_control())


extern void libvex_BackEnd(const VexTranslateArgs* vta,
    /*MOD*/ VexTranslateResult* res,
    /*MOD*/ IRSB* irsb,
    VexRegisterUpdates pxControl);

void libvex_BackEnd(const VexTranslateArgs* vta,
    /*MOD*/ VexTranslateResult* res,
    /*MOD*/ IRSB* irsb,
    VexRegisterUpdates pxControl)
{
    /* This the bundle of functions we need to do the back-end stuff
        (insn selection, reg-alloc, assembly) whilst being insulated
        from the target instruction set. */
    void         (*getRegUsage)  (HRegUsage*, const HInstr*, Bool);
    void         (*mapRegs)      (HRegRemap*, HInstr*, Bool);
    void         (*genSpill)     (HInstr**, HInstr**, HReg, Int, Bool);
    void         (*genReload)    (HInstr**, HInstr**, HReg, Int, Bool);
    HInstr* (*genMove)      (HReg, HReg, Bool);
    HInstr* (*directReload) (HInstr*, HReg, Short);
    void         (*ppInstr)      (const HInstr*, Bool);
    UInt(*ppReg)        (HReg);
    HInstrArray* (*iselSB)       (const IRSB*, VexArch, const VexArchInfo*,
        const VexAbiInfo*, Int, Int, Bool, Bool,
        Addr);
    Int(*emit)         ( /*MB_MOD*/Bool*,
        UChar*, Int, const HInstr*, Bool, VexEndness,
        const void*, const void*, const void*,
        const void*);
    Bool(*preciseMemExnsFn) (Int, Int, VexRegisterUpdates);

    const RRegUniverse* rRegUniv = NULL;

    Bool            mode64, chainingAllowed;
    Int             i, j, k, out_used;
    Int guest_sizeB;
    Int offB_HOST_EvC_COUNTER;
    Int offB_HOST_EvC_FAILADDR;
    Addr            max_ga;
    UChar           insn_bytes[128];
    HInstrArray* vcode;
    HInstrArray* rcode;

    getRegUsage = NULL;
    mapRegs = NULL;
    genSpill = NULL;
    genReload = NULL;
    genMove = NULL;
    directReload = NULL;
    ppInstr = NULL;
    ppReg = NULL;
    iselSB = NULL;
    emit = NULL;

    mode64 = False;
    chainingAllowed = False;
    guest_sizeB = 0;
    offB_HOST_EvC_COUNTER = 0;
    offB_HOST_EvC_FAILADDR = 0;
    preciseMemExnsFn = NULL;

    vassert(vta->disp_cp_xassisted != NULL);



    /* Both the chainers and the indir are either NULL or non-NULL. */
    if (vta->disp_cp_chain_me_to_slowEP != NULL) {
        vassert(vta->disp_cp_chain_me_to_fastEP != NULL);
        vassert(vta->disp_cp_xindir != NULL);
        chainingAllowed = True;
    }
    else {
        vassert(vta->disp_cp_chain_me_to_fastEP == NULL);
        vassert(vta->disp_cp_xindir == NULL);
    }

    switch (vta->arch_guest) {

    case VexArchX86:
        preciseMemExnsFn
            = X86FN(guest_x86_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestX86State);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestX86State, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestX86State, host_EvC_FAILADDR);
        break;

    case VexArchAMD64:
        preciseMemExnsFn
            = AMD64FN(guest_amd64_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestAMD64State);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestAMD64State, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestAMD64State, host_EvC_FAILADDR);
        break;

    case VexArchPPC32:
        preciseMemExnsFn
            = PPC32FN(guest_ppc32_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestPPC32State);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestPPC32State, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestPPC32State, host_EvC_FAILADDR);
        break;

    case VexArchPPC64:
        preciseMemExnsFn
            = PPC64FN(guest_ppc64_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestPPC64State);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestPPC64State, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestPPC64State, host_EvC_FAILADDR);
        break;

    case VexArchS390X:
        preciseMemExnsFn
            = S390FN(guest_s390x_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestS390XState);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestS390XState, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestS390XState, host_EvC_FAILADDR);
        break;

    case VexArchARM:
        preciseMemExnsFn
            = ARMFN(guest_arm_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestARMState);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestARMState, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestARMState, host_EvC_FAILADDR);
        break;

    case VexArchARM64:
        preciseMemExnsFn
            = ARM64FN(guest_arm64_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestARM64State);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestARM64State, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestARM64State, host_EvC_FAILADDR);
        break;

    case VexArchMIPS32:
        preciseMemExnsFn
            = MIPS32FN(guest_mips32_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestMIPS32State);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestMIPS32State, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestMIPS32State, host_EvC_FAILADDR);
        break;

    case VexArchMIPS64:
        preciseMemExnsFn
            = MIPS64FN(guest_mips64_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestMIPS64State);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestMIPS64State, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestMIPS64State, host_EvC_FAILADDR);
        break;

    case VexArchNANOMIPS:
        preciseMemExnsFn
            = NANOMIPSFN(guest_mips32_state_requires_precise_mem_exns);
        guest_sizeB = sizeof(VexGuestMIPS32State);
        offB_HOST_EvC_COUNTER = offsetof(VexGuestMIPS32State, host_EvC_COUNTER);
        offB_HOST_EvC_FAILADDR = offsetof(VexGuestMIPS32State, host_EvC_FAILADDR);
        break;

    default:
        vpanic("LibVEX_Codegen: unsupported guest insn set");
    }


    switch (vta->arch_host) {

    case VexArchX86:
        mode64 = False;
        rRegUniv = X86FN(getRRegUniverse_X86());
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) X86FN(getRegUsage_X86Instr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) X86FN(mapRegs_X86Instr);
        genSpill = CAST_TO_TYPEOF(genSpill) X86FN(genSpill_X86);
        genReload = CAST_TO_TYPEOF(genReload) X86FN(genReload_X86);
        genMove = CAST_TO_TYPEOF(genMove) X86FN(genMove_X86);
        directReload = CAST_TO_TYPEOF(directReload) X86FN(directReload_X86);
        ppInstr = CAST_TO_TYPEOF(ppInstr) X86FN(ppX86Instr);
        ppReg = CAST_TO_TYPEOF(ppReg) X86FN(ppHRegX86);
        iselSB = X86FN(iselSB_X86);
        emit = CAST_TO_TYPEOF(emit) X86FN(emit_X86Instr);
        vassert(vta->archinfo_host.endness == VexEndnessLE);
        break;

    case VexArchAMD64:
        mode64 = True;
        rRegUniv = AMD64FN(getRRegUniverse_AMD64());
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) AMD64FN(getRegUsage_AMD64Instr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) AMD64FN(mapRegs_AMD64Instr);
        genSpill = CAST_TO_TYPEOF(genSpill) AMD64FN(genSpill_AMD64);
        genReload = CAST_TO_TYPEOF(genReload) AMD64FN(genReload_AMD64);
        genMove = CAST_TO_TYPEOF(genMove) AMD64FN(genMove_AMD64);
        directReload = CAST_TO_TYPEOF(directReload) AMD64FN(directReload_AMD64);
        ppInstr = CAST_TO_TYPEOF(ppInstr) AMD64FN(ppAMD64Instr);
        ppReg = CAST_TO_TYPEOF(ppReg) AMD64FN(ppHRegAMD64);
        iselSB = AMD64FN(iselSB_AMD64);
        emit = CAST_TO_TYPEOF(emit) AMD64FN(emit_AMD64Instr);
        vassert(vta->archinfo_host.endness == VexEndnessLE);
        break;

    case VexArchPPC32:
        mode64 = False;
        rRegUniv = PPC32FN(getRRegUniverse_PPC(mode64));
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) PPC32FN(getRegUsage_PPCInstr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) PPC32FN(mapRegs_PPCInstr);
        genSpill = CAST_TO_TYPEOF(genSpill) PPC32FN(genSpill_PPC);
        genReload = CAST_TO_TYPEOF(genReload) PPC32FN(genReload_PPC);
        genMove = CAST_TO_TYPEOF(genMove) PPC32FN(genMove_PPC);
        ppInstr = CAST_TO_TYPEOF(ppInstr) PPC32FN(ppPPCInstr);
        ppReg = CAST_TO_TYPEOF(ppReg) PPC32FN(ppHRegPPC);
        iselSB = PPC32FN(iselSB_PPC);
        emit = CAST_TO_TYPEOF(emit) PPC32FN(emit_PPCInstr);
        vassert(vta->archinfo_host.endness == VexEndnessBE);
        break;

    case VexArchPPC64:
        mode64 = True;
        rRegUniv = PPC64FN(getRRegUniverse_PPC(mode64));
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) PPC64FN(getRegUsage_PPCInstr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) PPC64FN(mapRegs_PPCInstr);
        genSpill = CAST_TO_TYPEOF(genSpill) PPC64FN(genSpill_PPC);
        genReload = CAST_TO_TYPEOF(genReload) PPC64FN(genReload_PPC);
        genMove = CAST_TO_TYPEOF(genMove) PPC64FN(genMove_PPC);
        ppInstr = CAST_TO_TYPEOF(ppInstr) PPC64FN(ppPPCInstr);
        ppReg = CAST_TO_TYPEOF(ppReg) PPC64FN(ppHRegPPC);
        iselSB = PPC64FN(iselSB_PPC);
        emit = CAST_TO_TYPEOF(emit) PPC64FN(emit_PPCInstr);
        vassert(vta->archinfo_host.endness == VexEndnessBE ||
            vta->archinfo_host.endness == VexEndnessLE);
        break;

    case VexArchS390X:
        mode64 = True;
        rRegUniv = S390FN(getRRegUniverse_S390());
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) S390FN(getRegUsage_S390Instr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) S390FN(mapRegs_S390Instr);
        genSpill = CAST_TO_TYPEOF(genSpill) S390FN(genSpill_S390);
        genReload = CAST_TO_TYPEOF(genReload) S390FN(genReload_S390);
        genMove = CAST_TO_TYPEOF(genMove) S390FN(genMove_S390);
        directReload = CAST_TO_TYPEOF(directReload) S390FN(directReload_S390);
        ppInstr = CAST_TO_TYPEOF(ppInstr) S390FN(ppS390Instr);
        ppReg = CAST_TO_TYPEOF(ppReg) S390FN(ppHRegS390);
        iselSB = S390FN(iselSB_S390);
        emit = CAST_TO_TYPEOF(emit) S390FN(emit_S390Instr);
        vassert(vta->archinfo_host.endness == VexEndnessBE);
        break;

    case VexArchARM:
        mode64 = False;
        rRegUniv = ARMFN(getRRegUniverse_ARM());
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) ARMFN(getRegUsage_ARMInstr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) ARMFN(mapRegs_ARMInstr);
        genSpill = CAST_TO_TYPEOF(genSpill) ARMFN(genSpill_ARM);
        genReload = CAST_TO_TYPEOF(genReload) ARMFN(genReload_ARM);
        genMove = CAST_TO_TYPEOF(genMove) ARMFN(genMove_ARM);
        ppInstr = CAST_TO_TYPEOF(ppInstr) ARMFN(ppARMInstr);
        ppReg = CAST_TO_TYPEOF(ppReg) ARMFN(ppHRegARM);
        iselSB = ARMFN(iselSB_ARM);
        emit = CAST_TO_TYPEOF(emit) ARMFN(emit_ARMInstr);
        vassert(vta->archinfo_host.endness == VexEndnessLE);
        break;

    case VexArchARM64:
        mode64 = True;
        rRegUniv = ARM64FN(getRRegUniverse_ARM64());
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) ARM64FN(getRegUsage_ARM64Instr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) ARM64FN(mapRegs_ARM64Instr);
        genSpill = CAST_TO_TYPEOF(genSpill) ARM64FN(genSpill_ARM64);
        genReload = CAST_TO_TYPEOF(genReload) ARM64FN(genReload_ARM64);
        genMove = CAST_TO_TYPEOF(genMove) ARM64FN(genMove_ARM64);
        ppInstr = CAST_TO_TYPEOF(ppInstr) ARM64FN(ppARM64Instr);
        ppReg = CAST_TO_TYPEOF(ppReg) ARM64FN(ppHRegARM64);
        iselSB = ARM64FN(iselSB_ARM64);
        emit = CAST_TO_TYPEOF(emit) ARM64FN(emit_ARM64Instr);
        vassert(vta->archinfo_host.endness == VexEndnessLE);
        break;

    case VexArchMIPS32:
        mode64 = False;
        rRegUniv = MIPS32FN(getRRegUniverse_MIPS(mode64));
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) MIPS32FN(getRegUsage_MIPSInstr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) MIPS32FN(mapRegs_MIPSInstr);
        genSpill = CAST_TO_TYPEOF(genSpill) MIPS32FN(genSpill_MIPS);
        genReload = CAST_TO_TYPEOF(genReload) MIPS32FN(genReload_MIPS);
        genMove = CAST_TO_TYPEOF(genMove) MIPS32FN(genMove_MIPS);
        ppInstr = CAST_TO_TYPEOF(ppInstr) MIPS32FN(ppMIPSInstr);
        ppReg = CAST_TO_TYPEOF(ppReg) MIPS32FN(ppHRegMIPS);
        iselSB = MIPS32FN(iselSB_MIPS);
        emit = CAST_TO_TYPEOF(emit) MIPS32FN(emit_MIPSInstr);
        vassert(vta->archinfo_host.endness == VexEndnessLE
            || vta->archinfo_host.endness == VexEndnessBE);
        break;

    case VexArchMIPS64:
        mode64 = True;
        rRegUniv = MIPS64FN(getRRegUniverse_MIPS(mode64));
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) MIPS64FN(getRegUsage_MIPSInstr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) MIPS64FN(mapRegs_MIPSInstr);
        genSpill = CAST_TO_TYPEOF(genSpill) MIPS64FN(genSpill_MIPS);
        genReload = CAST_TO_TYPEOF(genReload) MIPS64FN(genReload_MIPS);
        genMove = CAST_TO_TYPEOF(genMove) MIPS64FN(genMove_MIPS);
        ppInstr = CAST_TO_TYPEOF(ppInstr) MIPS64FN(ppMIPSInstr);
        ppReg = CAST_TO_TYPEOF(ppReg) MIPS64FN(ppHRegMIPS);
        iselSB = MIPS64FN(iselSB_MIPS);
        emit = CAST_TO_TYPEOF(emit) MIPS64FN(emit_MIPSInstr);
        vassert(vta->archinfo_host.endness == VexEndnessLE
            || vta->archinfo_host.endness == VexEndnessBE);
        break;

    case VexArchNANOMIPS:
        mode64 = False;
        rRegUniv = NANOMIPSFN(getRRegUniverse_NANOMIPS(mode64));
        getRegUsage
            = CAST_TO_TYPEOF(getRegUsage) NANOMIPSFN(getRegUsage_NANOMIPSInstr);
        mapRegs = CAST_TO_TYPEOF(mapRegs) NANOMIPSFN(mapRegs_NANOMIPSInstr);
        genSpill = CAST_TO_TYPEOF(genSpill) NANOMIPSFN(genSpill_NANOMIPS);
        genReload = CAST_TO_TYPEOF(genReload) NANOMIPSFN(genReload_NANOMIPS);
        genMove = CAST_TO_TYPEOF(genMove) NANOMIPSFN(genMove_NANOMIPS);
        ppInstr = CAST_TO_TYPEOF(ppInstr) NANOMIPSFN(ppNANOMIPSInstr);
        ppReg = CAST_TO_TYPEOF(ppReg) NANOMIPSFN(ppHRegNANOMIPS);
        iselSB = NANOMIPSFN(iselSB_NANOMIPS);
        emit = CAST_TO_TYPEOF(emit) NANOMIPSFN(emit_NANOMIPSInstr);
        vassert(vta->archinfo_host.endness == VexEndnessLE
            || vta->archinfo_host.endness == VexEndnessBE);
        break;

    default:
        vpanic("LibVEX_Translate: unsupported host insn set");
    }

    // Are the host's hardware capabilities feasible. The function will
    // not return if hwcaps are infeasible in some sense.
    //check_hwcaps(vta->arch_host, vta->archinfo_host.hwcaps);


    /* Turn it into virtual-registerised code.  Build trees -- this
        also throws away any dead bindings. */
    max_ga = ado_treebuild_BB(irsb, preciseMemExnsFn, pxControl);

    if (vta->finaltidy) {
        irsb = vta->finaltidy(irsb);
    }

    vexAllocSanityCheck();

    if (vex_traceflags & VEX_TRACE_TREES) {
        vex_printf("\n------------------------"
            "  After tree-building "
            "------------------------\n\n");
        ppIRSB(irsb);
        vex_printf("\n");
    }

    /* HACK */
    if (0) {
        *(vta->host_bytes_used) = 0;
        res->status = VexTransOK; return;
    }
    /* end HACK */

    if (vex_traceflags & VEX_TRACE_VCODE)
        vex_printf("\n------------------------"
            " Instruction selection "
            "------------------------\n");

    /* No guest has its IP field at offset zero.  If this fails it
        means some transformation pass somewhere failed to update/copy
        irsb->offsIP properly. */
    vassert(irsb->offsIP >= 16);

    vcode = iselSB(irsb, vta->arch_host,
        &vta->archinfo_host,
        &vta->abiinfo_both,
        offB_HOST_EvC_COUNTER,
        offB_HOST_EvC_FAILADDR,
        chainingAllowed,
        vta->addProfInc,
        max_ga);

    vexAllocSanityCheck();

    if (vex_traceflags & VEX_TRACE_VCODE)
        vex_printf("\n");

    if (vex_traceflags & VEX_TRACE_VCODE) {
        for (i = 0; i < vcode->arr_used; i++) {
            vex_printf("%3d   ", i);
            ppInstr(vcode->arr[i], mode64);
            vex_printf("\n");
        }
        vex_printf("\n");
    }

    /* Register allocate. */
    RegAllocControl con = {
        .univ = rRegUniv, .getRegUsage = getRegUsage, .mapRegs = mapRegs,
        .genSpill = genSpill, .genReload = genReload, .genMove = genMove,
        .directReload = directReload, .guest_sizeB = guest_sizeB,
        .ppInstr = ppInstr, .ppReg = ppReg, .mode64 = mode64 };
    switch (vex_control.regalloc_version) {
    case 2:
        rcode = doRegisterAllocation_v2(vcode, &con);
        break;
    case 3:
        rcode = doRegisterAllocation_v3(vcode, &con);
        break;
    default:
        vassert(0);
    }

    vexAllocSanityCheck();

    if (vex_traceflags & VEX_TRACE_RCODE) {
        vex_printf("\n------------------------"
            " Register-allocated code "
            "------------------------\n\n");
        for (i = 0; i < rcode->arr_used; i++) {
            vex_printf("%3d   ", i);
            ppInstr(rcode->arr[i], mode64);
            vex_printf("\n");
        }
        vex_printf("\n");
    }

    /* HACK */
    if (0) {
        *(vta->host_bytes_used) = 0;
        res->status = VexTransOK; return;
    }
    /* end HACK */

    /* Assemble */
    if (vex_traceflags & VEX_TRACE_ASM) {
        vex_printf("\n------------------------"
            " Assembly "
            "------------------------\n\n");
    }

    out_used = 0; /* tracks along the host_bytes array */
    for (i = 0; i < rcode->arr_used; i++) {
        HInstr* hi = rcode->arr[i];
        Bool    hi_isProfInc = False;
        if (UNLIKELY(vex_traceflags & VEX_TRACE_ASM)) {
            ppInstr(hi, mode64);
            vex_printf("\n");
        }
        j = emit(&hi_isProfInc,
            insn_bytes, sizeof insn_bytes, hi,
            mode64, vta->archinfo_host.endness,
            vta->disp_cp_chain_me_to_slowEP,
            vta->disp_cp_chain_me_to_fastEP,
            vta->disp_cp_xindir,
            vta->disp_cp_xassisted);
        if (UNLIKELY(vex_traceflags & VEX_TRACE_ASM)) {
            for (k = 0; k < j; k++)
                vex_printf("%02x ", (UInt)insn_bytes[k]);
            vex_printf("\n\n");
        }
        if (UNLIKELY(out_used + j > vta->host_bytes_size)) {
            vexSetAllocModeTEMP_and_clear();
            vex_traceflags = 0;
            res->status = VexTransOutputFull;
            return;
        }
        if (UNLIKELY(hi_isProfInc)) {
            vassert(vta->addProfInc); /* else where did it come from? */
            vassert(res->offs_profInc == -1); /* there can be only one (tm) */
            vassert(out_used >= 0);
            res->offs_profInc = out_used;
        }
        { UChar* dst = &vta->host_bytes[out_used];
        for (k = 0; k < j; k++) {
            dst[k] = insn_bytes[k];
        }
        out_used += j;
        }
    }
    *(vta->host_bytes_used) = out_used;

    vexAllocSanityCheck();

    vexSetAllocModeTEMP_and_clear();

    if (vex_traceflags) {
        /* Print the expansion ratio for this SB. */
        j = 0; /* total guest bytes */
        for (i = 0; i < vta->guest_extents->n_used; i++) {
            j += vta->guest_extents->len[i];
        }
        if (1) vex_printf("VexExpansionRatio %d %d   %d :10\n\n",
            j, out_used, (10 * out_used) / (j == 0 ? 1 : j));
    }

    //vex_traceflags = 0;
    res->status = VexTransOK;
    return;
}


/* Exported to library client. */

VexTranslateResult LibVEX_Translate( /*MOD*/ VexTranslateArgs* vta)
{
    VexTranslateResult res = { 0 };
    VexRegisterUpdates pxControl = VexRegUpd_INVALID;

    IRSB* irsb = LibVEX_FrontEnd(vta, &res, &pxControl);
    libvex_BackEnd(vta, &res, irsb, pxControl);
    return res;
}





#endif