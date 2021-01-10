
/* ---------------------------------------------------------------------------------------
 *      Notify-bibi Symbolic-Emulation-Engine project
 *      Copyright (c) 2019 Microsoft Corporation by notify-bibi@github, 2496424084@qq.com
 *      ALL RIGHTS RESERVED.
 *
 *      采用模拟执行 为宿主机提供的c代码 来操作客户机的内存和寄存器（宿主机和主机内存共享，
 *      通过执行该c代码来访问 如VexGuestX86State参数来修改宿主机寄存器，将宿主机寄存器页
 *      挂载到irdirty环境）
 *      解决ir_dirty的函数不支持符号执行问题，解决大量适配问题
 * ---------------------------------------------------------------------------------------
 */



#include "engine/ir_dirty.h"
#include "engine/state_class.h"
#include "engine/z3_target_call/z3_target_call.h"

#ifdef _DEBUG
//#define OUTPUT_STMTS
#endif

using namespace TR;
//注意地址位宽
void tAMD64REGS(int offset, int length);

namespace Drt {

    __declspec(align(32))
        class IRDirtyMode : private EmuEnvironment {

        template<typename THword>
        IRDirtyMode(TR::vex_info const& info, MEM<THword>& mem_obj, VexArch host) :EmuEnvironment(info, mem_obj, host) {};

        template<typename THword>
        IRSB* translate_front(MEM<THword>& mem, Addr guest_addr) {

            VexRegisterUpdates pxControl;
            VexTranslateResult res;
            IRSB* cache_irsb = irsbCache.find(mem, guest_addr);
            if (LIKELY(cache_irsb != nullptr)) {
                return cache_irsb;
            }

            VexTranslateArgs* vta = get_ir_vex_translate_args();
            const UChar* bytes_insn = guest_addr;
            set_guest_bytes_addr(bytes_insn, guest_addr);
            IRSB* irsb = LibVEX_FrontEnd(vta, &res, &pxControl);
            irsbCache.push(irsb, LibVEX_IRSB_transfer());
            return irsb;
        }



    };


   
}



template<typename ADDR>
DirtyCtx dirty_context(State<ADDR>* s) {
   // return (DirtyCtx)new VexIRDirty<ADDR>(*s);
}
template<typename ADDR>
Addr64 dirty_get_gsptr(DirtyCtx dctx) {
   // return ((VexIRDirty<ADDR>*)dctx)->getGSPTR();
}
template<typename ADDR>
void dirty_context_del(DirtyCtx dctx) {
    //delete ((VexIRDirty<ADDR>*)dctx);
}

template<typename ADDR>
void dirty_ccall(DirtyCtx dctx, IRCallee* cee, IRExpr** args) {
    //VexIRDirty<ADDR>* d = (VexIRDirty<ADDR>*)dctx;
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    //vexSetAllocModeTEMP_and_save_curr();
    //d->init_param(cee, args);
   // d->start();
}

template<typename ADDR>
void dirty_call_np(DirtyCtx dctx, const HChar* name, void* func, const std::initializer_list<rsval<Addr64>>& parms) {
    //VexIRDirty<ADDR>* d = (VexIRDirty<ADDR>*)dctx;
    IRCallee cee = { (Int)parms.size() , name, func, 0xffffffff };
   // vexSetAllocModeTEMP_and_save_curr();
   // d->init_param(&cee, parms);
   // d->start();
}

template<typename ADDR>
void dirty_run(DirtyCtx dctx, IRDirty* dirty) {
    //VexIRDirty<ADDR>* d = (VexIRDirty<ADDR>*)dctx;
    //dirty_ccall<ADDR>(dctx, dirty->cee, dirty->args);
}

template<typename ADDR>
tval dirty_result(DirtyCtx dctx, IRType rty) {
    //VexIRDirty<ADDR>* d = (VexIRDirty<ADDR>*)dctx;
    //return d->result(rty);
}


/*


    ctx64 v(VexArchAMD64, "");
    TR::EmuEnvironment emu_ev(v, mem, VexArchAMD64);
    IRSB* bb = emu_ev.translate_front(mem, (Addr)func);











*/






IRSB* redundant_code_removal_BB(IRSB* bb) {
    
}






#if 1



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

template DirtyCtx dirty_context(State<Addr32>* s);
template DirtyCtx dirty_context(State<Addr64>* s);
template Addr64 dirty_get_gsptr<Addr32>(DirtyCtx dctx);
template Addr64 dirty_get_gsptr<Addr64>(DirtyCtx dctx);
template void dirty_run<Addr32>(DirtyCtx dctx, IRDirty* dirty);
template void dirty_run<Addr64>(DirtyCtx dctx, IRDirty* dirty);
template void dirty_context_del<Addr32>(DirtyCtx dctx);
template void dirty_context_del<Addr64>(DirtyCtx dctx);
template void dirty_ccall<Addr32>(DirtyCtx dctx, IRCallee* cee, IRExpr** args);
template void dirty_ccall<Addr64>(DirtyCtx dctx, IRCallee* cee, IRExpr** args);
template void dirty_call_np<Addr32>(DirtyCtx dctx, const HChar* name, void* func, const std::initializer_list<rsval<Addr64>>& parms);
template void dirty_call_np<Addr64>(DirtyCtx dctx, const HChar* name, void* func, const std::initializer_list<rsval<Addr64>>& parms);
template tval dirty_result<Addr32>(DirtyCtx dctx, IRType rty);
template tval dirty_result<Addr64>(DirtyCtx dctx, IRType rty);

#endif