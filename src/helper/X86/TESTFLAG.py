# -*- encoding: utf-8 -*-
from __future__ import print_function
from capstone import *
from keystone import *
from capstone.x86 import *
cs = Cs(CS_ARCH_X86, CS_MODE_64)
cs.detail = True

def asm(string,address):
    try:
        ks = Ks(KS_ARCH_X86, KS_MODE_64)
        encoding, count = ks.asm(string, address)
    except KsError as e:
        # keep the below code for debugging
        #print("Keypatch Error: {0}".format(e))
        #print("Original asm: {0}".format(assembly))
        #print("Fixed up asm: {0}".format(fix_ida_syntax(assembly)))
        encoding, count = None, 0
    return (encoding, count)


regs={'rax': (16, 8), 'eax': (16, 4), 'ax': (16, 2), 'al': (16, 1), 'ah': (17, 1), 'rcx': (24, 8), 'ecx': (24, 4), 'cx': (24, 2), 'cl': (24, 1), 'ch': (25, 1), 'rdx': (32, 8), 'edx': (32, 4), 'dx': (32, 2), 'dl': (32, 1), 'dh': (33, 1), 'rbx': (40, 8), 'ebx': (40, 4), 'bx': (40, 2), 'bl': (40, 1), 'bh': (41, 1), 'rsp': (48, 8), 'sp': (48, 8), 'esp': (48, 4), 'rbp': (56, 8), 'bp': (56, 8), 'ebp': (56, 4), 'rsi': (64, 8), 'esi': (64, 4), 'si': (64, 2), 'sil': (64, 1), 'sih': (65, 1), 'rdi': (72, 8), 'edi': (72, 4), 'di': (72, 2), 'dil': (72, 1), 'dih': (73, 1), 'r8': (80, 8), 'r9': (88, 8), 'r10': (96, 8), 'r11': (104, 8), 'r12': (112, 8), 'r13': (120, 8), 'r14': (128, 8), 'r15': (136, 8), 'cc_op': (144, 8), 'cc_dep1': (152, 8), 'cc_dep2': (160, 8), 'cc_ndep': (168, 8), 'd': (176, 8), 'dflag': (176, 8), 'rip': (184, 8), 'ip': (184, 8), 'pc': (184, 8), 'ac': (192, 8), 'acflag': (192, 8), 'id': (200, 8), 'idflag': (200, 8), 'fs': (208, 8), 'fs_const': (208, 8), 'sseround': (216, 8), 'ymm0': (224, 32), 'xmm0': (224, 16), 'ymm1': (256, 32), 'xmm1': (256, 16), 'ymm2': (288, 32), 'xmm2': (288, 16), 'ymm3': (320, 32), 'xmm3': (320, 16), 'ymm4': (352, 32), 'xmm4': (352, 16), 'ymm5': (384, 32), 'xmm5': (384, 16), 'ymm6': (416, 32), 'xmm6': (416, 16), 'ymm7': (448, 32), 'xmm7': (448, 16), 'ymm8': (480, 32), 'xmm8': (480, 16), 'ymm9': (512, 32), 'xmm9': (512, 16), 'ymm10': (544, 32), 'xmm10': (544, 16), 'ymm11': (576, 32), 'xmm11': (576, 16), 'ymm12': (608, 32), 'xmm12': (608, 16), 'ymm13': (640, 32), 'xmm13': (640, 16), 'ymm14': (672, 32), 'xmm14': (672, 16), 'ymm15': (704, 32), 'xmm15': (704, 16), 'ymm16': (736, 32), 'xmm16': (736, 16), 'ftop': (768, 4), 'fpreg': (776, 64), 'fpu_regs': (776, 64), 'mm0': (776, 8), 'mm1': (784, 8), 'mm2': (792, 8), 'mm3': (800, 8), 'mm4': (808, 8), 'mm5': (816, 8), 'mm6': (824, 8), 'mm7': (832, 8), 'fptag': (840, 8), 'fpu_tags': (840, 8), 'fpround': (848, 8), 'fc3210': (856, 8), 'emnote': (864, 4), 'cmstart': (872, 8), 'cmlen': (880, 8), 'nraddr': (888, 8), 'gs': (904, 8), 'gs_const': (904, 8), 'ip_at_syscall': (912, 8)}


flagop=["JE", "JNE", "JZ", "JNZ", "JS", "JNS", "JC", "JNC", "JO", "JNO", "JA", "JNA", "JAE", "JNAE", "JG", "JNG", "JGE", "JNGE", "JB", "JNB", "JBE", "JNBE", "JL", "JNL", "JLE", "JNLE", "JP", "JNP", "JPE", "JPO"]


for op in flagop:
    offset=0
    for cmp_reg in ["rax, rbx","eax, ebx","ax, bx","al, bl"]:
        cmp_regA,cmp_regB=cmp_reg.split(", ")
        string="""cmp {} 
         jmp addr
         addr:
          {} 0x{:x} """.format(cmp_reg,op,0x4009ff)
        encoding, count=asm(string,0x400946);
        if(encoding):
            code=""
            for b in encoding:
                code+="\\x{:02x}".format(b)
            cmp_regA_offset,cmp_regA_size=regs[cmp_regA]
            cmp_regB_offset,cmp_regB_size=regs[cmp_regB]
            C1="""
            auto AX = m_ctx.bv_const("AX", {});
            regs.Ist_Put<e_symbolic>({},Variable(m_ctx,AX,{}));
            """.format(cmp_regA_size*8,cmp_regA_offset,cmp_regA_size*8)

            C2="""
            auto BX = m_ctx.bv_const("BX", {});
            regs.Ist_Put<e_symbolic>({},Variable(m_ctx,BX,{}));
            """.format(cmp_regB_size*8,cmp_regB_offset,cmp_regB_size*8)

            C3='''
            auto page = getMemPage(0x0400946);
            char code[]={"%s"};
            for(int i=0;i<=sizeof(code);i++){
                page->unit->m_bytes[0x946 + i]=(UChar)code[i];
            }
            '''%(code)

            print(string)
            print(C3)
            print(C1)
            print(C2)
        else:
            print(string)