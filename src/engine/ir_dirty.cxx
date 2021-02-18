
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
#include "engine/state_explorer.h"
#include "engine/z3_target_call/z3_target_call.h"
#include "pub/gen_global_var_call.hpp"

#ifdef _DEBUG
//#define OUTPUT_STMTS
#endif

using namespace TR;
//注意地址位宽
void tAMD64REGS(int offset, int length);

extern void bb_insn_control_obj_set(void* instance, const UChar* (*guest_insn_control_method)(void*, Addr, Long, const UChar*));
static const UChar* host_insn_control_method(void*, Addr guest_IP_sbstart, Long delta, const UChar* host_code) {
    return host_code;
}

namespace TR {

    // dirty
    class EmuEnvHost : public EmuEnvironment {
        static constexpr VexArch host = VexArchAMD64;
        static constexpr ULong traceflags = 0;
        static thread_local IR_Manager static_dirty_ir_temp;
        IR_Manager& m_ir_temp;
    public:
        EmuEnvHost(z3::vcontext& ctx) : EmuEnvironment(host, traceflags), m_ir_temp(static_dirty_ir_temp) { }


        void set_guest_bb_insn_control_obj() override;
        //new ir temp
        virtual void malloc_ir_buff(Z3_context ctx) override;
        //free ir temp
        virtual void free_ir_buff() override;
        // host dirty fuc translate
        IRSB* translate_front(HWord /*dirty/guest_addr*/) override;
        virtual sv::tval& operator[](UInt idx) override;
    };

    thread_local IR_Manager EmuEnvHost::static_dirty_ir_temp;

    // ------------------------EmuEnvHost--------------------------

    void EmuEnvHost::set_guest_bb_insn_control_obj()
    {
        bb_insn_control_obj_set(nullptr, host_insn_control_method);
    }

    void EmuEnvHost::malloc_ir_buff(Z3_context ctx)
    {


    }

    void EmuEnvHost::free_ir_buff()
    {
    }

    IRSB* dirty_code_deal_BB(IRSB* bb) {
        //ppIRSB(bb);
        Int i;
        for (i = 0; i < bb->stmts_used; i++) {
            IRStmt* st = bb->stmts[i];

            if (st->tag == Ist_NoOp)
                continue;

            /* Deal with Gets -> load */
            if (st->tag == Ist_WrTmp && st->Ist.WrTmp.data->tag == Iex_Get) {
                IRExpr* get = st->Ist.WrTmp.data;
                get->Iex.Get.offset += 0x400;
            }

            if (st->tag == Ist_WrTmp && st->Ist.WrTmp.data->tag == Iex_GetI) {
                IRExpr* get = st->Ist.WrTmp.data;
                get->Iex.GetI.descr->base += 0x400;
            }

            if (st->tag == Ist_Put) {
                st->Ist.Put.offset += 0x400;
            };
            
            if (st->tag == Ist_PutI) {
                st->Ist.PutI.details->descr->base += 0x400;
            }


            if (st->tag == Ist_WrTmp && st->Ist.WrTmp.data->tag == Iex_Load) {
                IRExpr* load = st->Ist.WrTmp.data;
                if (load->Iex.Load.addr->tag == Iex_Const) {
                    load->Iex.Load.addr->Iex.Const.con->Ico.U64 |= 1ull << 56;
                }
            }

        } /* for (i = 0; i < bb->stmts_used; i++) */


        //ppIRSB(bb);
        return bb;
    }

    IRSB* EmuEnvHost::translate_front(HWord ea)
    {
        VexRegisterUpdates pxControl;
        VexTranslateResult res;
        IRSB* cache_irsb = find(ea);
        if (LIKELY(cache_irsb != nullptr)) {
            return cache_irsb;
        }
        VexTranslateArgs* vta = get_ir_vex_translate_args();
        set_guest_bytes_addr((const UChar*)ea, ea);
        IRSB* irsb = LibVEX_FrontEnd(vta, &res, &pxControl);

        irsb = dirty_code_deal_BB(irsb);
        //irsbCache.push(irsb, LibVEX_IRSB_transfer());
        return irsb;

    }
    sv::tval& EmuEnvHost::operator[](UInt idx)
    {
        return m_ir_temp[idx];
    }
}


class VexIRDirty {
    static constexpr VexArch host_arch =  VexArchAMD64;
    static constexpr Addr64 m_stack_addr = (0x7fll << 56);
    static constexpr Addr64 m_guest_regs_map_addr = (0x80ull << 56) | 0x0;
    static constexpr Addr64 vex_ret_addr = (0x1ull << 56) | 0xfa1e;
    static constexpr Addr64 vex_host_reg_base = 0x400;
    State& m_state;
    //当前dirty func的入口点
    HWord        m_host_OEP; // 虚拟 OEP
    //host rip（计数器eip）
    HWord        m_host_ip;    // 虚拟 IP
    Addr64       m_stack_reserve_size = 0x1000;
public:
    VexIRDirty(State& s) 
        :m_state(s)
    {
        //m_stack_addr = s.mem.find_block_reverse((Addr64)0 - 0x1000, m_stack_reserve_size);
        //m_guest_regs_map_addr = s.mem.find_block_forward(0x1000, REGISTER_LEN);
        s.mem.map(m_stack_addr, m_stack_reserve_size);
    };

    Addr64 getGSPTR() { return 0; }

    void   set_ip(UChar* Haddr) {
        m_host_OEP = (HWord)Haddr;
    };
    void init_param(const IRCallee* cee, IRExpr** const exp_args) {
        set_ip((UChar*)cee->addr);
        Addr64 stack_ret = m_stack_addr + m_stack_reserve_size - 0x8ull * MAX_GUEST_DIRTY_CALL_PARARM_NUM;
        m_state.regs.set(vex_host_reg_base + AMD64_IR_OFFSET::RAX, -1ll);
        m_state.regs.set(vex_host_reg_base + AMD64_IR_OFFSET::RSP, stack_ret);
        m_state.regs.set(vex_host_reg_base + AMD64_IR_OFFSET::RBP, 0x233ull);
        //code : call cee->addr
        m_state.mem.store(stack_ret, vex_ret_addr);

        {
            //x64 fastcall 
            const UInt assembly_args[] = { AMD64_IR_OFFSET::RCX, AMD64_IR_OFFSET::RDX, AMD64_IR_OFFSET::R8, AMD64_IR_OFFSET::R9 };
            UInt i;
            for (i = 0; exp_args[i] != NULL; i++) {
                tval short_v = m_state.tIRExpr(exp_args[i]);
                auto v = short_v.zext(64 - short_v.nbits()).tors<false, 64>();
                if (i >= (sizeof(assembly_args) / sizeof(UInt))) {
                    m_state.mem.store(stack_ret + (ULong)(i << 3), v);
                }
                else {
                    m_state.regs.set(vex_host_reg_base + assembly_args[i], v);
                }
            };
            vassert(i <= MAX_GUEST_DIRTY_CALL_PARARM_NUM);
        };
    }

    void init_param(const IRCallee* cee, const std::initializer_list<rsval<Addr64>>& exp_args) {
        set_ip((UChar*)cee->addr);
        Addr64 stack_ret = m_stack_addr + m_stack_reserve_size - 0x8ull * MAX_GUEST_DIRTY_CALL_PARARM_NUM;
        m_state.regs.set(vex_host_reg_base + AMD64_IR_OFFSET::RAX, -1ll);
        m_state.regs.set(vex_host_reg_base + AMD64_IR_OFFSET::RSP, stack_ret);
        m_state.regs.set(vex_host_reg_base + AMD64_IR_OFFSET::RBP, 0x233ull);

        //code : call cee->addr
        m_state.mem.store(stack_ret, vex_ret_addr);
        {
            //x64 fastcall 
            const UInt assembly_args[] = { AMD64_IR_OFFSET::RCX, AMD64_IR_OFFSET::RDX, AMD64_IR_OFFSET::R8, AMD64_IR_OFFSET::R9 };
            auto v = exp_args.begin();
            UInt i;
            for (i = 0; i != exp_args.size(); i++, v++) {
                if (i >= (sizeof(assembly_args) / sizeof(UInt))) {
                    m_state.mem.store(stack_ret + (ULong)(i << 3), *v);
                }
                else {
                    //m_state.regs.set(assembly_args[i], *v);
                    m_state.regs.set(vex_host_reg_base + assembly_args[i], *v);
                }
            };
            vassert(i <= MAX_GUEST_DIRTY_CALL_PARARM_NUM);
        };
    };

    void start() {
        if (m_state.is_dirty_mode()) {
            // state.vex -> dirty-vex ->  dirty-vex
            m_state.set_status(DirtyRecursiveExec);
            return;
        }
        vex_info saved_vinfo = m_state.vinfo();
        m_state.vinfo() = vex_info(host_arch);
        
        TRControlFlags savedTraceFlag = (TRControlFlags)m_state.getFlags();
        //m_state.setFlags(CF_None);
        m_state.setFlags(CF_traceJmp);
        EmuEnvironment* saved_guest_irvex = &m_state.irvex();
        m_state.set_dirty_mode();
        EmuEnvHost ir(m_state.ctx());
        ir.set_guest_bb_insn_control_obj();
        m_host_ip = m_host_OEP;
        m_state.start(m_host_ip , &ir);

        m_state.set_irvex(saved_guest_irvex);
        m_state.clean_dirty_mode();
        m_state.setFlags(savedTraceFlag);

        m_state.vinfo() = saved_vinfo;
        //m_state.vinfo()
    }

    tval result(IRType ty) { return m_state.regs.Iex_Get(vex_host_reg_base + AMD64_IR_OFFSET::RAX, ty); };
    ~VexIRDirty() {}
};




DirtyCtx dirty_context(State* s) {
    return (DirtyCtx)new VexIRDirty(*s);
}


Addr64 dirty_get_gsptr(DirtyCtx dctx) {
    return ((VexIRDirty*)dctx)->getGSPTR();
}


void dirty_context_del(DirtyCtx dctx) {
    delete ((VexIRDirty*)dctx);
}


void dirty_ccall(DirtyCtx dctx, const IRCallee* cee, IRExpr** const args) {
    VexIRDirty* d = (VexIRDirty*)dctx;
    Int regparms = cee->regparms;
    UInt mcx_mask = cee->mcx_mask;
    //vexSetAllocModeTEMP_and_save_curr();
    d->init_param(cee, args);
    d->start();
}


void dirty_call_np(DirtyCtx dctx, const HChar* name, void* func, const std::initializer_list<rsval<Addr64>>& parms) {
    VexIRDirty* d = (VexIRDirty*)dctx;
    IRCallee cee = { (Int)parms.size() , name, func, 0xffffffff };
    //vexSetAllocModeTEMP_and_save_curr();
    d->init_param(&cee, parms);
    d->start();
}


void dirty_run(DirtyCtx dctx, const IRDirty* dirty) {
    //VexIRDirty* d = (VexIRDirty*)dctx;
    dirty_ccall(dctx, dirty->cee, dirty->args);
}


tval dirty_result(DirtyCtx dctx, IRType rty) {
    VexIRDirty* d = (VexIRDirty*)dctx;
    return d->result(rty);
}







//
//IRSB* redundant_code_removal_BB(IRSB* bb) {
//    
//}
//





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



#endif
