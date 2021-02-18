# encoding:utf-8
from __future__ import print_function
import idaapi
import idc
import ida_dbg
import ida_bytes
from idautils import cpu
import ida_loader
import idautils
import sys
import struct
import time
import re
# pip install pyvex<=8.18.10.5
# import pyvex
# import archinfo  # 没有pyvex则archinfo无法工作

import ctypes
import re
import base64
import keystone


arch = None
mode = None
GDT_MAP_ADDR = (1<<47) | 0xfff00000

FSMSR = 0xC0000100
GSMSR = 0xC0000101

BPNORMAL = 0
BPHARDWARE = 1
UE_HARDWARE_EXECUTE = 4
UE_HARDWARE_WRITE = 5
UE_HARDWARE_READWRITE = 6
UE_HARDWARE_SIZE_1 = 7
UE_HARDWARE_SIZE_2 = 8
UE_HARDWARE_SIZE_4 = 9
UE_HARDWARE_SIZE_8 = 10

amd64_rnames = {"rax": (16, 8), "rcx": (24, 8), "rdx": (32, 8), "rbx": (40, 8), "rsp": (48, 8), "rbp": (56, 8), "rsi": (64, 8), "rdi": (72, 8), "r8": (80, 8), "r9": (88, 8), "r10": (96, 8), "r11": (104, 8), "r12": (112, 8), "r13": (120, 8), "r14": (128, 8), "r15": (136, 8), "cc_op": (144, 8), "cc_dep1": (152, 8), "cc_dep2": (160, 8), "cc_ndep": (168, 8), "dflag": (176, 8), "rip": (184, 8), "acflag": (192, 8), "idflag": (200, 8), "fs_const": (208, 8), "sseround": (216, 8), "ymm0": (224, 32), "ymm1": (256, 32), "ymm2": (288, 32), "ymm3": (320, 32), "ymm4": (352, 32), "ymm5": (384, 32), "ymm6": (416, 32), "ymm7": (448, 32), "ymm8": (480, 32), "ymm9": (512, 32), "ymm10": (544, 32), "ymm11": (576, 32), "ymm12": (608, 32), "ymm13": (640, 32), "ymm14": (672, 32), "ymm15": (704, 32), "ymm16": (736, 32), "ftop": (768, 4), "fpreg": (776, 64), "fptag": (840, 8), "fpround": (848, 8), "fc3210": (856, 8), "emnote": (864, 4), "cmstart": (872, 8), "cmlen": (880, 8), "nraddr": (888, 8), "sc_class": (896, 8), "gs_const": (904, 8), "ip_at_syscall": (912, 8), "ldt": (920, 8), "gdt": (928, 8), "cs": (936, 2), "ds": (938, 2), "es": (940, 2), "fs": (942, 2), "gs": (944, 2), "ss": (946, 2)}
ppc_rnames = {'gpr0': (16, 8), 'r0': (16, 8), 'gpr1': (24, 8), 'r1': (24, 8), 'sp': (24, 8), 'gpr2': (32, 8), 'r2': (32, 8), 'rtoc': (32, 8), 'gpr3': (40, 8), 'r3': (40, 8), 'gpr4': (48, 8), 'r4': (48, 8), 'gpr5': (56, 8), 'r5': (56, 8), 'gpr6': (64, 8), 'r6': (64, 8), 'gpr7': (72, 8), 'r7': (72, 8), 'gpr8': (80, 8), 'r8': (80, 8), 'gpr9': (88, 8), 'r9': (88, 8), 'gpr10': (96, 8), 'r10': (96, 8), 'gpr11': (104, 8), 'r11': (104, 8), 'gpr12': (112, 8), 'r12': (112, 8), 'gpr13': (120, 8), 'r13': (120, 8), 'gpr14': (128, 8), 'r14': (128, 8), 'gpr15': (136, 8), 'r15': (136, 8), 'gpr16': (144, 8), 'r16': (144, 8), 'gpr17': (152, 8), 'r17': (152, 8), 'gpr18': (160, 8), 'r18': (160, 8), 'gpr19': (168, 8), 'r19': (168, 8), 'gpr20': (176, 8), 'r20': (176, 8), 'gpr21': (184, 8), 'r21': (184, 8), 'gpr22': (192, 8), 'r22': (192, 8), 'gpr23': (200, 8), 'r23': (200, 8), 'gpr24': (208, 8), 'r24': (208, 8), 'gpr25': (216, 8), 'r25': (216, 8), 'gpr26': (224, 8), 'r26': (224, 8), 'gpr27': (232, 8), 'r27': (232, 8), 'gpr28': (240, 8), 'r28': (240, 8), 'gpr29': (248, 8), 'r29': (248, 8), 'gpr30': (256, 8), 'r30': (256, 8), 'gpr31': (264, 8), 'r31': (264, 8), 'bp': (264, 8), 'vsr0': (272, 16), 'v0': (272, 16), 'fpr0': (272, 8), 'vsr1': (288, 16), 'v1': (288, 16), 'fpr1': (288, 8), 'vsr2': (304, 16), 'v2': (304, 16), 'fpr2': (304, 8), 'vsr3': (320, 16), 'v3': (320, 16), 'fpr3': (320, 8), 'vsr4': (336, 16), 'v4': (336, 16), 'fpr4': (336, 8), 'vsr5': (352, 16), 'v5': (352, 16), 'fpr5': (352, 8), 'vsr6': (368, 16), 'v6': (368, 16), 'fpr6': (368, 8), 'vsr7': (384, 16), 'v7': (384, 16), 'fpr7': (384, 8), 'vsr8': (400, 16), 'v8': (400, 16), 'fpr8': (400, 8), 'vsr9': (416, 16), 'v9': (416, 16), 'fpr9': (416, 8), 'vsr10': (432, 16), 'v10': (432, 16), 'fpr10': (432, 8), 'vsr11': (448, 16), 'v11': (448, 16), 'fpr11': (448, 8), 'vsr12': (464, 16), 'v12': (464, 16), 'fpr12': (464, 8), 'vsr13': (480, 16), 'v13': (480, 16), 'fpr13': (480, 8), 'vsr14': (496, 16), 'v14': (496, 16), 'fpr14': (496, 8), 'vsr15': (512, 16), 'v15': (512, 16), 'fpr15': (512, 8), 'vsr16': (528, 16), 'v16': (528, 16), 'fpr16': (528, 8), 'vsr17': (544, 16), 'v17': (544, 16), 'fpr17': (544, 8), 'vsr18': (560, 16), 'v18': (560, 16), 'fpr18': (560, 8), 'vsr19': (576, 16), 'v19': (576, 16), 'fpr19': (576, 8), 'vsr20': (592, 16), 'v20': (592, 16), 'fpr20': (592, 8), 'vsr21': (608, 16), 'v21': (608, 16), 'fpr21': (608, 8), 'vsr22': (624, 16), 'v22': (624, 16), 'fpr22': (624, 8), 'vsr23': (640, 16), 'v23': (640, 16), 'fpr23': (640, 8), 'vsr24': (656, 16), 'v24': (656, 16), 'fpr24': (656, 8), 'vsr25': (672, 16), 'v25': (672, 16), 'fpr25': (672, 8), 'vsr26': (688, 16), 'v26': (688, 16), 'fpr26': (688, 8), 'vsr27': (704, 16), 'v27': (704, 16), 'fpr27': (704, 8), 'vsr28': (720, 16), 'v28': (720, 16), 'fpr28': (720, 8), 'vsr29': (736, 16), 'v29': (736, 16), 'fpr29': (736, 8), 'vsr30': (752, 16), 'v30': (752, 16), 'fpr30': (752, 8), 'vsr31': (768, 16), 'v31': (768, 16), 'fpr31': (768, 8), 'vsr32': (784, 16), 'v32': (784, 16), 'vsr33': (800, 16), 'v33': (800, 16), 'vsr34': (816, 16), 'v34': (816, 16), 'vsr35': (832, 16), 'v35': (832, 16), 'vsr36': (848, 16), 'v36': (848, 16), 'vsr37': (864, 16), 'v37': (864, 16), 'vsr38': (880, 16), 'v38': (880, 16), 'vsr39': (896, 16), 'v39': (896, 16), 'vsr40': (912, 16), 'v40': (912, 16), 'vsr41': (928, 16), 'v41': (928, 16), 'vsr42': (944, 16), 'v42': (944, 16), 'vsr43': (960, 16), 'v43': (960, 16), 'vsr44': (976, 16), 'v44': (976, 16), 'vsr45': (992, 16), 'v45': (992, 16), 'vsr46': (1008, 16), 'v46': (1008, 16), 'vsr47': (1024, 16), 'v47': (1024, 16), 'vsr48': (1040, 16), 'v48': (1040, 16), 'vsr49': (1056, 16), 'v49': (1056, 16), 'vsr50': (1072, 16), 'v50': (1072, 16), 'vsr51': (1088, 16), 'v51': (1088, 16), 'vsr52': (1104, 16), 'v52': (1104, 16), 'vsr53': (1120, 16), 'v53': (1120, 16), 'vsr54': (1136, 16), 'v54': (1136, 16), 'vsr55': (1152, 16), 'v55': (1152, 16), 'vsr56': (1168, 16), 'v56': (1168, 16), 'vsr57': (1184, 16), 'v57': (1184, 16), 'vsr58': (1200, 16), 'v58': (1200, 16), 'vsr59': (1216, 16), 'v59': (1216, 16), 'vsr60': (1232, 16), 'v60': (1232, 16), 'vsr61': (1248, 16), 'v61': (1248, 16), 'vsr62': (1264, 16), 'v62': (1264, 16), 'vsr63': (1280, 16), 'v63': (1280, 16), 'cia': (1296, 8), 'ip': (1296, 8), 'pc': (1296, 8), 'lr': (1304, 8), 'ctr': (1312, 8), 'xer_so': (1320, 1), 'xer_ov': (1321, 1), 'xer_ca': (1322, 1), 'xer_bc': (1323, 1), 'cr0_321': (1324, 1), 'cr0_0': (1325, 1), 'cr0': (1325, 1), 'cr1_321': (1326, 1), 'cr1_0': (1327, 1), 'cr1': (1327, 1), 'cr2_321': (1328, 1), 'cr2_0': (1329, 1), 'cr2': (1329, 1), 'cr3_321': (1330, 1), 'cr3_0': (1331, 1), 'cr3': (1331, 1), 'cr4_321': (1332, 1), 'cr4_0': (1333, 1), 'cr4': (1333, 1), 'cr5_321': (1334, 1), 'cr5_0': (1335, 1), 'cr5': (1335, 1), 'cr6_321': (1336, 1), 'cr6_0': (1337, 1), 'cr6': (1337, 1), 'cr7_321': (1338, 1), 'cr7_0': (1339, 1), 'cr7': (1339, 1), 'fpround': (1340, 1), 'dfpround': (1341, 1), 'c_fpcc': (1342, 1), 'vrsave': (1344, 4), 'vscr': (1348, 4), 'emnote': (1352, 4), 'cmstart': (1360, 8), 'cmlen': (1368, 8), 'nraddr': (1376, 8), 'nraddr_gpr2': (1384, 8), 'redir_sp': (1392, 8), 'redir_stack': (1400, 256), 'ip_at_syscall': (1656, 8), 'sprg3_ro': (1664, 8), 'tfhar': (1672, 8), 'texasr': (1680, 8), 'tfiar': (1688, 8), 'ppr': (1696, 8), 'texasru': (1704, 4), 'pspb': (1708, 4)}
mips_rnames = {'zero': (16, 8), 'r0': (16, 8), 'at': (24, 8), 'r1': (24, 8), 'v0': (32, 8), 'r2': (32, 8), 'v1': (40, 8), 'r3': (40, 8), 'a0': (48, 8), 'r4': (48, 8), 'a1': (56, 8), 'r5': (56, 8), 'a2': (64, 8), 'r6': (64, 8), 'a3': (72, 8), 'r7': (72, 8), 't0': (80, 8), 'r8': (80, 8), 't1': (88, 8), 'r9': (88, 8), 't2': (96, 8), 'r10': (96, 8), 't3': (104, 8), 'r11': (104, 8), 't4': (112, 8), 'r12': (112, 8), 't5': (120, 8), 'r13': (120, 8), 't6': (128, 8), 'r14': (128, 8), 't7': (136, 8), 'r15': (136, 8), 's0': (144, 8), 'r16': (144, 8), 's1': (152, 8), 'r17': (152, 8), 's2': (160, 8), 'r18': (160, 8), 's3': (168, 8), 'r19': (168, 8), 's4': (176, 8), 'r20': (176, 8), 's5': (184, 8), 'r21': (184, 8), 's6': (192, 8), 'r22': (192, 8), 's7': (200, 8), 'r23': (200, 8), 't8': (208, 8), 'r24': (208, 8), 't9': (216, 8), 'r25': (216, 8), 'k0': (224, 8), 'r26': (224, 8), 'k1': (232, 8), 'r27': (232, 8), 'gp': (240, 8), 'r28': (240, 8), 'sp': (248, 8), 'r29': (248, 8), 's8': (256, 8), 'r30': (256, 8), 'fp': (256, 8), 'bp': (256, 8), 'ra': (264, 8), 'r31': (264, 8), 'lr': (264, 8), 'pc': (272, 8), 'ip': (272, 8), 'hi': (280, 8), 'lo': (288, 8), 'f0': (296, 8), 'f1': (304, 8), 'f2': (312, 8), 'f3': (320, 8), 'f4': (328, 8), 'f5': (336, 8), 'f6': (344, 8), 'f7': (352, 8), 'f8': (360, 8), 'f9': (368, 8), 'f10': (376, 8), 'f11': (384, 8), 'f12': (392, 8), 'f13': (400, 8), 'f14': (408, 8), 'f15': (416, 8), 'f16': (424, 8), 'f17': (432, 8), 'f18': (440, 8), 'f19': (448, 8), 'f20': (456, 8), 'f21': (464, 8), 'f22': (472, 8), 'f23': (480, 8), 'f24': (488, 8), 'f25': (496, 8), 'f26': (504, 8), 'f27': (512, 8), 'f28': (520, 8), 'f29': (528, 8), 'f30': (536, 8), 'f31': (544, 8), 'fir': (552, 4), 'fccr': (556, 4), 'fexr': (560, 4), 'fenr': (564, 4), 'fcsr': (568, 4), 'cp0_status': (572, 4), 'ulr': (576, 8), 'emnote': (584, 4), 'cond': (588, 4), 'cmstart': (592, 8), 'cmlen': (600, 8), 'nraddr': (608, 8), 'ip_at_syscall': (616, 8)}
s390_rnames = {'ia': (336, 8), 'ip': (336, 8), 'pc': (336, 8), 'r0': (192, 8), 'r1': (200, 8), 'r2': (208, 8), 'r3': (216, 8), 'r4': (224, 8), 'r5': (232, 8), 'r6': (240, 8), 'r7': (248, 8), 'r8': (256, 8), 'r9': (264, 8), 'r10': (272, 8), 'r11': (280, 8), 'bp': (280, 8), 'r12': (288, 8), 'r13': (296, 8), 'r14': (304, 8), 'r15': (312, 8), 'sp': (312, 8), 'f0': (64, 8), 'f1': (72, 8), 'f2': (80, 8), 'f3': (88, 8), 'f4': (96, 8), 'f5': (104, 8), 'f6': (112, 8), 'f7': (120, 8), 'f8': (128, 8), 'f9': (136, 8), 'f10': (144, 8), 'f11': (152, 8), 'f12': (160, 8), 'f13': (168, 8), 'f14': (176, 8), 'f15': (184, 8), 'a0': (0, 4), 'a1': (4, 4), 'a2': (8, 4), 'a3': (12, 4), 'a4': (16, 4), 'a5': (20, 4), 'a6': (24, 4), 'a7': (28, 4), 'a8': (32, 4), 'a9': (36, 4), 'a10': (40, 4), 'a11': (44, 4), 'a12': (48, 4), 'a13': (52, 4), 'a14': (56, 4), 'a15': (60, 4), 'nraddr': (384, 8), 'cmstart': (392, 8), 'cmlen': (400, 8), 'ip_at_syscall': (408, 8), 'emnote': (416, 4)} 

        
def convert_f80le_to_f64le(f80):
    # Bool  isInf;
    # Int   bexp, i, j;
    # UChar sign;
    isInf = None
    f64 = [None for i in range(8)]
    toUChar = lambda x: x & 0xff

    sign = toUChar((f80[9] >> 7) & 1);
    bexp = ((f80[9]) << 8) | f80[8];
    bexp &= 0x7FFF;

    """ If the exponent is zero, either we have a zero or a denormal.
      But an extended precision denormal becomes a double precision
      zero, so in either case, just produce the appropriately signed
      zero. """
    if (bexp == 0):
        f64[7] = toUChar(sign << 7);
        f64[6] = f64[5] = f64[4] = f64[3] = f64[2] = f64[1] = f64[0] = 0;
        return f64;

    """ If the exponent is 7FFF, this is either an Infinity, a SNaN or
      QNaN, as determined by examining bits 62:0, thus:
          10  ... 0    Inf
          10X ... X    SNaN
          11X ... X    QNaN
      where at least one of the Xs is not zero.
    """
    if (bexp == 0x7FFF):
        isInf = (f80[7] & 0x7F) == 0 and f80[6] == 0 and f80[5] == 0 and f80[4] == 0 and f80[3] == 0 and f80[2] == 0 and \
                f80[1] == 0 and f80[0] == 0

        if (isInf):
            if (0 == (f80[7] & 0x80)):
                # goto wierd_NaN;
                f64[7] = (1 << 7) | 0x7F;
                f64[6] = 0xF8;
                f64[5] = f64[4] = f64[3] = f64[2] = f64[1] = f64[0] = 0;
                return f64;
            """ Produce an appropriately signed infinity:
                S 1-=11 (11)  0-=10 (52)
            """
            f64[7] = toUChar((sign << 7) | 0x7F);
            f64[6] = 0xF0;
            f64[5] = f64[4] = f64[3] = f64[2] = f64[1] = f64[0] = 0;
            return f64;

        """ So it's either a QNaN or SNaN.  Distinguish by considering
            bit 61.  Note, this destroys all the trailing bits
            (identity?) of the NaN.  IEEE754 doesn't require preserving
            these (it only requires that there be one QNaN value and one
            SNaN value), but x87 does seem to have some ability to
            preserve them.  Anyway, here, the NaN's identity is
            destroyed.  Could be improved. """
        if (f80[7] & 0x40):
            """ QNaN.  Make a canonical QNaN:
                S 1-=11 (11)  1  0-=10 (51) 
            """
            f64[7] = toUChar((sign << 7) | 0x7F);
            f64[6] = 0xF8;
            f64[5] = f64[4] = f64[3] = f64[2] = f64[1] = f64[0] = 0x00;
        else:
            """ SNaN.  Make a SNaN:
                S 1-=11 (11)  0  1-=11 (51) 
            """
            f64[7] = toUChar((sign << 7) | 0x7F);
            f64[6] = 0xF7;
            f64[5] = f64[4] = f64[3] = f64[2] = f64[1] = f64[0] = 0xFF;

        return f64;

    """ If it's not a Zero, NaN or Inf, and the integer part (bit 62) is
      zero, the x87 FPU appears to consider the number denormalised
      and converts it to a QNaN. """
    if (0 == (f80[7] & 0x80)):
        # wierd_NaN:
        # /* Strange hardware QNaN:
        # S 1-=11 (11)  1  0-=10 (51) 
        # */
        # /* On a PIII, these QNaNs always appear with sign==1.  I have
        # no idea why. */
        f64[7] = (1 << 7) | 0x7F;
        f64[6] = 0xF8;
        f64[5] = f64[4] = f64[3] = f64[2] = f64[1] = f64[0] = 0;
        return f64;

    """It's not a zero, denormal, infinity or nan.  So it must be a 
      normalised number.  Rebias the exponent and consider. """
    bexp -= (16383 - 1023);
    if (bexp >= 0x7FF):
        """ It's too big for a double.  Construct an infinity. """
        f64[7] = toUChar((sign << 7) | 0x7F);
        f64[6] = 0xF0;
        f64[5] = f64[4] = f64[3] = f64[2] = f64[1] = f64[0] = 0;
        return f64;

    if (bexp <= 0):
        """ It's too small for a normalised double.  First construct a
        zero and then see if it can be improved into a denormal.  """
        f64[7] = toUChar(sign << 7);
        f64[6] = f64[5] = f64[4] = f64[3] = f64[2] = f64[1] = f64[0] = 0;

        if (bexp < -52):
            """ Too small even for a denormal. """
            return f64;

        """ Ok, let's make a denormal.  Note, this is SLOW. */
        /* Copy bits 63, 62, 61, etc of the src mantissa into the dst, 
            indexes 52+bexp, 51+bexp, etc, until k+bexp < 0. */
        /* bexp is in range -52 .. 0 inclusive """
        i = 63
        while (i >= 0):
            j = i - 12 + bexp;
            if (j < 0):
                break
            """ We shouldn't really call vassert from generated code. """
            assert (j >= 0 and j < 52);
            write_bit_array(f64,
                            j,
                            read_bit_array(f80, i));
            i -= 1

        """and now we might have to round ..."""
        if (read_bit_array(f80, 10 + 1 - bexp) == 1):
            if (f64[0] != 0xFF):
                f64[0] += 1;

            elif (f64[0] == 0xFF and f64[1] != 0xFF):
                f64[0] = 0
                f64[1] += 1

            elif (f64[0] == 0xFF and f64[1] == 0xFF and f64[2] != 0xFF):
                f64[0] = 0
                f64[1] = 0
                f64[2] += 1

        return f64;

    """ Ok, it's a normalised number which is representable as a double.
    Copy the exponent and mantissa into place. */
    """

    f64[0] = toUChar((f80[1] >> 3) | (f80[2] << 5));
    f64[1] = toUChar((f80[2] >> 3) | (f80[3] << 5));
    f64[2] = toUChar((f80[3] >> 3) | (f80[4] << 5));
    f64[3] = toUChar((f80[4] >> 3) | (f80[5] << 5));
    f64[4] = toUChar((f80[5] >> 3) | (f80[6] << 5));
    f64[5] = toUChar((f80[6] >> 3) | (f80[7] << 5));

    f64[6] = toUChar(((bexp << 4) & 0xF0) | ((f80[7] >> 3) & 0x0F));

    f64[7] = toUChar((sign << 7) | ((bexp >> 4) & 0x7F));

    """ Now consider any rounding that needs to happen as a result of
    truncating the mantissa. """
    if (f80[1] & 4):

        """ If the bottom bits of f80 are "100 0000 0000", then the
        infinitely precise value is deemed to be mid-way between the
        two closest representable values.  Since we're doing
        round-to-nearest (the default mode), in that case it is the
        bit immediately above which indicates whether we should round
        upwards or not -=1 if 0, we don't.  All that is encapsulated
        in the following simple test. """
        if ((f80[1] & 0xF) == 4 and f80[0] == 0):
            return f64;

        # do_rounding:
        """ Round upwards.  This is a kludge.  Once in every 2^24
        roundings (statistically) the bottom three bytes are all 0xFF
        and so we don't round at all.  Could be improved. """
        if (f64[0] != 0xFF):
            f64[0] += 1;

        elif (f64[0] == 0xFF and f64[1] != 0xFF):
            f64[0] = 0
            f64[1] += 1

        elif (f64[0] == 0xFF and f64[1] == 0xFF and f64[2] != 0xFF):
            f64[0] = 0
            f64[1] = 0
            f64[2] += 1

            """ else we don't round, but we should. """
    return f64
    
    
def Breakpoints():
    count = idc.get_bpt_qty()
    for i in range(0, count):
        ea = idc.get_bpt_ea(i)
        bpt = idaapi.bpt_t()
        if not idaapi.get_bpt(ea, bpt):
            continue
        if bpt.type & idc.BPT_SOFT != 0:
            yield (ea, BPNORMAL, 0, idaapi.get_64bit(ea))
        else:
            bptype = BPNORMAL if bpt.type == idc.BPT_DEFAULT else BPHARDWARE
            hwtype = {
                idc.BPT_WRITE: UE_HARDWARE_WRITE,
                idc.BPT_RDWR: UE_HARDWARE_READWRITE,
                idc.BPT_EXEC: UE_HARDWARE_EXECUTE
            }[bpt.type]
            hwsize = {
                1: UE_HARDWARE_SIZE_1,
                2: UE_HARDWARE_SIZE_2,
                4: UE_HARDWARE_SIZE_4,
                8: UE_HARDWARE_SIZE_8,
            }[bpt.size]
            yield (ea, bptype, (hwtype << 4 | hwsize), 0)


class ArchInfo:
    def __init__(self, ks_arch, register_names):
        self.ks_arch = ks_arch
        self.register_names = register_names
        

class Dump:
    def __init__(self, arch_info, mode):
        self.arch_info = arch_info
        self.mode = mode
        self.mem_mmap = {}

    def Regs_register_names(self):
        return {}
        
    def getRegs(self):
        assert (0)

    def init_segm_mem(self):
        return {}
        
    @staticmethod
    def getDbgMem(ea, size):
        b = b''
        for i in range(0, (size & (~7)), 8):
            b += struct.pack("<Q", idc.get_qword(ea + i))

        for i in range(size & 7):
            b += struct.pack("<B", idaapi.get_byte(ea + (size & (~7)) + i))

        return b

    @staticmethod
    def getSegName(seg, segm):
        count = 0
        h = ''
        while (idaapi.get_segm_name(seg, 0) + h) in segm.keys():
            count += 1
            h = str(count)
        name = idaapi.get_segm_name(seg, 0) + h
        return name

    @staticmethod
    def getDbgMemPage(address, length):
        data = []
        L = 0
        data.append([idaapi.dbg_read_memory(address, 0x400 - (address & 0x3ff)), address, 0x400 - (address & 0x3ff)])
        L += data[-1][2]
        for ea in range((address + 0x400) & (~0x3ff), ((address + length) & (~0x3ff)), 0x400):
            data.append([idaapi.dbg_read_memory(ea, 0x400), ea, 0x400])
            L += 0x400
        data.append([idaapi.dbg_read_memory((address + length) & (~0x3ff), (address + length) & (0x3ff)),
                     (address + length) & (~0x3ff), (address + length) & (0x3ff)])
        L += data[-1][2]
        assert (L == length)
        return data

    @staticmethod
    def reg_ug_str_value2hex(v, f = lambda x : x):
        v = v.replace('`', "").split(" ")
        return f("".join(v[::-1]))
        
    @staticmethod
    def reg_ug_str_value_convert(orig, regvals_dict, f = lambda x : x):
        for rn, rv in regvals_dict.items():
            orig[rn] = f(Dump.reg_ug_str_value2hex(rv))
        return orig
        
    def writeMem(self, binfile):
        register_names = self.Regs_register_names()
        regs = self.getRegs()
        segm = self.init_segm_mem()
        
        # idc.get_bpt_qty() GetBptEA(n):
        nameoffset_p = 0
        dataoffset_p = 0
        all_ab_name = 0


        
        const_show_length = 0
        for n in range(idaapi.get_segm_qty()):
            seg = idaapi.getnseg(n)
            if seg:
                name = Dump.getSegName(seg, segm)
                if const_show_length<len(name):
                    const_show_length = len(name)
                    
        _len = const_show_length//2-2
        print("+ %s +----------------------+--------------------+----------+--------+"%("-"*const_show_length))
        print("| %s |          VA          |        size        |   flag   | status |"%(("-"*_len)+"segment"+"-"*(_len))[:const_show_length])
        print("+ %s +----------------------+--------------------+----------+--------+"%("-"*const_show_length))

        idaapi.refresh_debugger_memory()
        for n in range(idaapi.get_segm_qty()):
            seg = idaapi.getnseg(n)
            if seg:
                name = Dump.getSegName(seg, segm)
                address = seg.start_ea
                length = seg.end_ea - seg.start_ea

                db_data = idaapi.dbg_read_memory(address, length)
                print(("| %-"+str(const_show_length)+"s |  %18x  | %8x -> %5dkb|    %2d    |   ") % (
                name, address, length, length / 1024, seg.flags), end="")
                if db_data:
                    segm[name] = [address, length, db_data]
                    print('ok   |')
                    length = len(db_data)
                    segm[name] = [address, length, db_data]
                else:
                    if (length >= 0x400):
                        print(
                            "war  |\n+ %s +----------------------+--------------------+----------+--------+"%("-"*const_show_length))
                        data = Dump.getDbgMemPage(address, length)
                        data.append([b"", 0, 0])
                        is_unmap = False
                        tmp = b''
                        begin = address
                        fbegin = address
                        fsize = 0
                        for i, d in enumerate(data):
                            db, ea, size = d
                            if is_unmap:
                                if db:  # 0 1
                                    is_unmap = False
                                    begin = ea
                                    tmp = db
                                    print(("| %-"+str(const_show_length)+"s |  %18x  | %8x -> %5dkb|    %2d    |  faild |") % (
                                    name, fbegin, fsize, fsize / 1024, seg.flags))
                                else:  # 0 0
                                    fsize += size
                                    if (i == len(data) - 1):
                                        print(("| %-"+str(const_show_length)+"s |  %18x  | %8x -> %5dkb|    %2d    |  faild |") % (
                                        name, fbegin, fsize, fsize / 1024, seg.flags))
                                    pass
                            else:
                                if db:  # 1 1
                                    is_unmap = False
                                    tmp += db
                                else:  # 1 0
                                    fbegin = ea
                                    fsize = size
                                    is_unmap = True
                                    if tmp:
                                        name = Dump.getSegName(seg, segm)
                                        segm[name] = [begin, len(tmp), tmp]
                                        print(("| %-"+str(const_show_length)+"s |  %18x  | %8x -> %5dkb|    %2d    |   ok   |") % (
                                        name, begin, len(tmp), len(tmp) / 1024, seg.flags))
                                    else:
                                        print(("| %-"+str(const_show_length)+"s |  %18x  | %8x -> %5dkb|    %2d    |  faild |") % (
                                        name, fbegin, fsize, fsize / 1024, seg.flags))
                                        break

                        print("+ %s +----------------------+--------------------+----------+--------+"%("-"*const_show_length))
                    else:
                        print('  faild')
                    continue

        print("+ %s +----------------------+--------------------+----------+--------+"%("-"*const_show_length))
        
        for regName, INT  in regs.items():
            regAddress, size = register_names[regName]
            #print(regName)
            print(" (%-10s IR_offset: %-5d) (val: %32x nb: %2d) " % (regName, regAddress, (INT), size))
            up = None
            if INT < 0:
                up = lambda x: x.lower()
            else:
                up = lambda x: x

            try:
                if size == 1:
                    db_data = struct.pack(up("<B"), INT)
                elif size == 2:
                    db_data = struct.pack(up("<H"), INT)
                elif size == 4:
                    db_data = struct.pack(up("<I"), INT)
                elif size == 8:
                    db_data = struct.pack(up("<Q"), INT)
                elif size == 16:
                    db_data = struct.pack(up("<QQ"), int(INT & 0xffffffffffffffff), int(INT >> 64))
                elif size == 32:
                    db_data = struct.pack(up("<QQQQ"), INT & 0xffffffffffffffff, (INT >> 64) & 0xffffffffffffffff,
                                          (INT >> 128) & 0xffffffffffffffff, INT >> 192)
                else:
                    continue
                segm['registers' + str(regAddress)] = [regAddress, len(db_data), db_data]
            except Exception as e:
                print("-=1-=1-=1-=1- error:", e, regName, hex(INT), size, "-=1-=1-=1-=1- ")

        
        
        def find_segm(va, length, bpt_l):
            global BPNORMAL
            for ea, bptype, hwtype_hwsize, code in bpt_l:
                if va <= ea and ea < va + length:
                    if bptype == BPNORMAL:
                        yield (code, ea - va)

        bpt_list = [i for i in Breakpoints()]
        for name in segm:
            address, length, db_data = segm[name]
            ab_name = (name + '\x00').encode('utf-8')
            all_ab_name += len(ab_name)
            # 将软件断点pass掉
            len_db_data = len(db_data)
            for code, offset in find_segm(address, length, bpt_list):
                bpt_code = db_data[offset:offset+8]
                db_data = db_data[:offset] + struct.pack("<Q", code) + db_data[offset + 8:]
                segm[name] = [address, length, db_data]
                assert (len(db_data) == len_db_data)
                print ("bkp found: address: %x : bpt_mem -%s- <= +%s+"%(address+offset, bpt_code.hex(), struct.pack("<Q", code).hex()))


        for name in segm:
            address, length, db_data = segm[name]
            ab_name = (name + '\x00').encode('utf-8')
            nameoffset = len(segm) * 32 + nameoffset_p
            dataoffset = len(segm) * 32 + all_ab_name + dataoffset_p
            db1 = struct.pack("<Q", nameoffset)
            db2 = struct.pack("<Q", address)
            db3 = struct.pack("<Q", length)
            db4 = struct.pack("<Q", dataoffset)
            self.mem_mmap[name] = [address, dataoffset, length]
            binfile.write(db1)
            binfile.write(db2)
            binfile.write(db3)
            binfile.write(db4)
            nameoffset_p += len(ab_name)
            dataoffset_p += length
        for name in segm:
            address, length, db_data = segm[name]
            ab_name = (name + '\x00').encode('utf-8')
            binfile.write(ab_name)
        for name in segm:
            address, length, db_data = segm[name]
            binfile.write(db_data)

    def init_segm_mem(self):
        return {}


class gdt32():
    def __init__(self, GDT_ADDR_write):
        self.SegDiscriptions = {}
        self.gdt = []
        self.GDT_SIZE = 0
        self.GDT_ADDR_write = GDT_ADDR_write

    @staticmethod
    def create_selector(idx, TI, RPL):  # TI:1 LDT 0:GDT   PRL:最高级:00  11最低级
        to_ret = RPL & 0b11
        to_ret |= TI & 0b1 << 2
        to_ret |= (idx & 0b1111111111111) << 3
        return to_ret

    def segReg2base(self, reg):
        value = self.uc.reg_read(reg)
        try:
            return self.SegDiscriptions[value >> 3]
        except:
            return 0

    @staticmethod
    def create_gdt_entry(base, limit, DPL, S, TYPE, flags):
        to_ret = limit & 0xffff;  # [:16]      limit[:16]
        to_ret |= (base & 0xffffff) << 16;  # [16:40]    base[:24]
        to_ret |= (TYPE & 0xf) << 40;  # TYPE 段的类型特征和存取权限
        to_ret |= (S & 0xb1) << 44;  # S: 如果s=0 这是一个系统段 1 是普通代码段或数据段
        to_ret |= (DPL & 0xb11) << 45;  # DPL 描述符特权级 0~3
        to_ret |= (1 & 0xb1) << 47;  # 1
        to_ret |= ((limit >> 16) & 0xf) << 48;  # [48:52]    limit[16:20]: 存放段最后一个内存单元的偏移量
        to_ret |= (flags & 0xf) << 52;  # [52:56]    flag: G<<3|D<<2|0<1|AVL (各1bit )如果G=0那么段大小为0~1MB, G=1段大小为4KB~4GB  D或B 这个我还没搞懂 以后再说只要知道32位访问为1 AVL: linux忽略这个
        to_ret |= ((base >> 24) & 0xff) << 56;  # [56:64]    base[24:32]
        return struct.pack('<Q', to_ret)

    def addSegDiscription(self, GDT_index, base, limit, DPL, S, TYPE, flags):
        seg_selector = GDT_index
        seg_selector >>= 3
        if seg_selector >= self.GDT_SIZE:
            for c in range(seg_selector - self.GDT_SIZE + 1):
                self.gdt.append(None)
            self.GDT_SIZE = seg_selector
        self.gdt[seg_selector] = gdt32.create_gdt_entry(base, limit, DPL, S, TYPE, flags)

    def get_gdt(self):
        ret = b''
        for tab in self.gdt:
            if (tab):
                ret += tab
            else:
                ret += b"\x00\x00\x00\x00\x00\x00\x00\x00"
        return {"gdt_table": [self.GDT_ADDR_write, len(ret), ret]}


class AMD64_dump(Dump):
    def __init__(self, arch_info, mode):
        Dump.__init__(self, arch_info, mode)
        self.reg_vals = AMD64_dump.windbg_get_regs()
        
        
    def Regs_register_names(self):
        register_names = self.arch_info.register_names
        fpreg_off, fpreg_size = register_names["fpreg"]
        self.arch_info.register_names.pop("fpreg")
        for i in range(8):
            register_names["st%d" % i] = (fpreg_off + i * 8, 8)
        return register_names
        
    @staticmethod
    def _windbg_get_sreg_desc():
        # min 0 max 80
        cmdline = "dg 0 80"
        b, res = ida_dbg.send_dbg_command(cmdline)
        result = []
        for desc in res.split("\n"):
            # print(desc)
            regex = re.match(r'(?P<sel>[a-f0-9]+) (?P<base>[a-f0-9`]+) (?P<limit>[a-f0-9`]+)[\w| ]+ (?P<flags>[a-f0-9]+)', desc)
            if regex:
                reg = regex.groupdict()
                # print(reg)
                result.append(reg)
        return result
    
    
    @staticmethod
    def _windbg_get_teb64_gs_const():
        # min 0 max 80
        cmdline = "!teb"
        b, res = ida_dbg.send_dbg_command(cmdline)
        for line in res.split("\n"):
            # print(desc)
            regex = re.match(r'Wow64 TEB at (?P<teb>[a-f0-9]+)', line)
            if regex:
                teb = regex.groupdict()
                return int(teb["teb"], 16)
        return 0
        
    """
    https://docs.microsoft.com/zh-cn/windows-hardware/drivers/debugger/r--registers-
    WINDBG>rm?
           1 - Integer state (32-bit) or
           2 - Integer state (64-bit), 64-bit takes precedence
           4 - Floating-point state
           8 - Segment registers
          10 - MMX registers
          20 - Debug registers and, in kernel, CR4
          40 - SSE XMM registers
         200 - AVX YMM registers
         400 - AVX YMM Integer registers
         800 - AVX XMM Integer registers
        1000 - AVX-512 ZMM registers
        2000 - AVX-512 ZMM Integer registers
        4000 - AVX-512 Opmask registers
        8000 - Shadow Stack Registers
    """
    @staticmethod
    def _windbg_get_regs(mask):
        cmdline = "rm{:x}".format(mask)
        b, res = ida_dbg.send_dbg_command(cmdline)
        cmdline = "r"
        b, res = ida_dbg.send_dbg_command(cmdline)
        res = " ".join(res.split("\n")[:-2])
        # print(text)
        regex = re.findall(r'(?P<rn>[a-z]+[a-z0-9]*)=(?P<rv>[a-f0-9]+)', res)
        if regex:
            return dict(regex)
          
    @staticmethod  
    def _windbg_get_regs_same(regs, fms = "uq"):
        cmdline = "r {:}:type".format(":type, ".join(regs)).replace("type", fms)
        
        b, res = ida_dbg.send_dbg_command(cmdline)
        text = " ".join(res.split("\n")[:6])
        # print(text)
        regex = re.findall(r'(?P<rn>[a-z0-9]+)=(?P<rv>[a-f0-9 ]+)', text)
        if regex:
            reg = dict(regex)
            return reg
        print(cmdline)
        raise "error"


    @staticmethod   
    def _get_fpu_regs():
        fps = {}
        for rname in ["st%d"%n for n in range(8)]:
            cmdline = "r "+ rname
            b, res = ida_dbg.send_dbg_command(cmdline)
            regex = re.search(r'\((?P<sym>[a-f0-9]{1}):(?P<hi>[a-f0-9]{4}):(?P<lo>[a-f0-9]{16})\)', res, flags = re.DOTALL)
            if regex:
                val = regex.groupdict()
                val = val["hi"]+val["lo"]
                f80_l = bytes.fromhex(val)[::-1]
                f80 = int(val, 16);
                f64 = 0
                f64_l = convert_f80le_to_f64le(f80_l)
                for i in range(8):
                    f64 = (f64 << 8) | f64_l[7 - i]
                print(rname, hex(f80), hex(f64))
                fps[rname] = "%x"%f64
            else:
                print(cmdline, res, "error")
        return fps


    @staticmethod   
    def windbg_get_regs():
        general_state = AMD64_dump._windbg_get_regs(2)
        # fpcw fpsw fptw
        floating_state_fp = AMD64_dump._windbg_get_regs(4)
        # st0-st7
        floating_state_st = AMD64_dump._get_fpu_regs()
        # sregs cs ss ds es fs gs efl
        segment_registers = AMD64_dump._windbg_get_regs(8)
        # sreg_desc
        segment_desc = AMD64_dump._windbg_get_sreg_desc()
        # Ymm0-15
        AVX_state_st = AMD64_dump._windbg_get_regs_same(["ymm%s"%n for n in range(16)])
        # mm0-7
        MMX_registers = AMD64_dump._windbg_get_regs_same(["mm%s"%n for n in range(8)])
        # other DF
        other_regs = AMD64_dump._windbg_get_regs_same(["df"], fms = 'ud')
        
        return {"general":general_state, "fp":floating_state_fp, "st":floating_state_st, "sregs":segment_registers, "segm_desc":segment_desc, "avx":AVX_state_st, "mmx": MMX_registers, "other" : other_regs }
    
    
    
    
    def getRegs(self):
        reg_vals = {}
        f = lambda x : int(x, 16)
        reg_vals = Dump.reg_ug_str_value_convert(reg_vals, self.reg_vals["general"], f = f)
        reg_vals = Dump.reg_ug_str_value_convert(reg_vals, self.reg_vals["st"], f = f)
        reg_vals = Dump.reg_ug_str_value_convert(reg_vals, self.reg_vals["fp"], f = f)
        reg_vals = Dump.reg_ug_str_value_convert(reg_vals, self.reg_vals["sregs"], f = f)
        reg_vals = Dump.reg_ug_str_value_convert(reg_vals, self.reg_vals["avx"], f = f)
        reg_vals = Dump.reg_ug_str_value_convert(reg_vals, self.reg_vals["other"], f = f)
        
        # for rn, v in reg_vals.items():
        #    print(rn, v )
        reg_vals.pop("iopl")
        reg_vals.pop("efl")
        
        def getfpround(tag):
            return (tag >> 10) & 0b11


        def getSseRound(name):
            assert (name == 'sseround')
            return (idc.get_reg_value('MXCSR') >> 13) & 0b11


        def getftop(tag):
            # fld
            # dbgtop 0   7   6
            # dbgtag 00  80  0xc0
            # IRftop 8   7   6  
            dbgtop = (tag >> 11) & 0b111
            return  8 if dbgtop == 0 else dbgtop


        def getfpu_tags(tag):
            re = 0
            for i in range(8):
                f = ((tag >> i)&0b1) << (8 * i)
                re = (re) | f
            return re
            

        reg_vals['fptag'] = getfpu_tags(reg_vals['fptw'])
        reg_vals.pop("fptw")
        
        
        reg_vals['ftop'] = getftop(reg_vals['fpsw'])
        reg_vals.pop("fpsw")
        
        
        reg_vals['fpround'] = getfpround(reg_vals['fpcw'])
        reg_vals.pop("fpcw")
        
        reg_vals["sseround"] = getSseRound("sseround")
        
        reg_vals["gdt"] = GDT_MAP_ADDR
        
        reg_vals["dflag"] = -1 if reg_vals["df"] else 0x1
        reg_vals.pop("df")
        
        
        reg_vals['gs_const'] = AMD64_dump._windbg_get_teb64_gs_const()
        reg_vals['fs_const'] = 0
        
        print(reg_vals)
        return reg_vals

    def init_segm_mem(self):
        gdt = gdt32(GDT_MAP_ADDR)
        descs = self.reg_vals["segm_desc"]
        DPL = 1
        S = 0
        TYPE = 0
        for desc in descs:
            descs = Dump.reg_ug_str_value_convert({}, desc, lambda x:int(x, 16))
            sel, base, limit, flags = descs["sel"], descs["base"], descs["limit"], descs["flags"]
            print(".sel :{:x}  .base :0x{:x}  .limit :{:x}  .flags :{:x}".format(sel, base, limit, flags))
            gdt.addSegDiscription(sel, base, limit, DPL, S, TYPE, flags=flags)
        
        return gdt.get_gdt()
        
        
        
        
def get_hardware_mode():
    (arch, mode) = (None, None)
    info = idaapi.get_inf_structure()
    # heuristically detect hardware setup
    info = idaapi.get_inf_structure()
    dumper = None
    try:
        cpuname = info.procname.lower()
    except:
        cpuname = info.procName.lower()

    try:
        # since IDA7 beta 3 (170724) renamed inf.mf -> is_be()/set_be()
        is_be = idaapi.cvar.inf.is_be()
    except:
        # older IDA versions
        is_be = idaapi.cvar.inf.mf
    # print("Keypatch BIG_ENDIAN = %s" %is_be)
    # print("ArchInfo(\n    ", arch.register_names,",\n    ", arch.registers, ")")
    if cpuname == "metapc":
        if info.is_64bit():
            #arch = archinfo.ArchAMD64()
            arch = ArchInfo( keystone.KS_ARCH_X86, amd64_rnames)
            mode = keystone.KS_MODE_64
            dumper = AMD64_dump(arch, mode)
        elif info.is_32bit():
            #arch = archinfo.ArchX86()
            arch = ArchInfo( keystone.KS_ARCH_X86, amd64_rnames)
            mode = keystone.KS_MODE_32
            dumper = AMD64_dump(arch, mode)
        else:
            #arch = archinfo.ArchNotFound()
            arch = ArchInfo(keystone.KS_ARCH_X86, {}, {})
            mode = keystone.KS_MODE_16

    elif cpuname.startswith("ppc"):
        if info.is_64bit():
            # arch = archinfo.ArchPPC64()
            arch = ArchInfo(keystone.KS_ARCH_PPC, ppc_rnames)
            mode = keystone.KS_MODE_PPC64
        else:
            # arch = archinfo.ArchPPC32()
            arch = ArchInfo(keystone.KS_ARCH_PPC, ppc_rnames)
            mode = keystone.KS_MODE_PPC32
        if cpuname == "ppc":
            # do not support Little Endian mode for PPC
            mode += keystone.KS_MODE_BIG_ENDIAN

    elif cpuname.startswith("mips"):
        if info.is_64bit():
            # arch = archinfo.ArchMIPS64()
            arch = ArchInfo(keystone.KS_ARCH_MIPS, mips_rnames)
            mode = keystone.KS_MODE_MIPS64
        else:
            # arch = archinfo.ArchMIPS32()
            arch = ArchInfo(keystone.KS_ARCH_MIPS, mips_rnames)
            mode = keystone.KS_MODE_MIPS32
    elif cpuname.startswith("systemz") or cpuname.startswith("s390x"):
        # arch = archinfo.ArchS390X()
        arch = ArchInfo(keystone.KS_ARCH_S390, s390_rnames)
        mode = keystone.KS_MODE_BIG_ENDIAN

    return (dumper, arch, mode)


class memdumper(idaapi.plugin_t):
    flags = idaapi.PLUGIN_UNL
    comment = "This is a comment bin"

    help = "This is help bin"
    wanted_name = "Tr memdumper"
    wanted_hotkey = "Shift-3"

    def init(self):
        return idaapi.PLUGIN_OK

    def run(self, arg):
        dump_class_obj, arch, mode = get_hardware_mode()
        if not idaapi.is_debugger_on():
            idaapi.warning("tr : Please run the process first!")
            return
        if idaapi.get_process_state() != -1:
            idaapi.warning("tr : Please suspend the debugger first!")
            return
        
        bin_path = ida_loader.get_path(ida_loader.PATH_TYPE_CMD)
        bin_path = bin_path
        binfile = open(bin_path + '.dump', 'wb+')
        dump_class_obj.writeMem(binfile)
        binfile.close()
        print('dump success: ', bin_path + '.dump')

    def term(self):
        idaapi.msg("term() called!\n")


def PLUGIN_ENTRY():
    return memdumper()
