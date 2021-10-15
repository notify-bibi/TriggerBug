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
# pip install pyvex<=8.18.10.5
# import pyvex
# import archinfo  # 没有pyvex则archinfo无法工作

import ctypes
import re
import base64
import keystone

arch = None
mode = None
GDT_MAP_ADDR = 0xfff00000

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


# xxxxxxxxxxxxxxxxxxxxx X86 & AMD64 xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx

def getfpround(name):
    assert (name == 'fpround')
    return (idc.get_reg_value('CTRL') >> 10) & 0b11


def getSseRound(name):
    assert (name == 'sseround')
    return (idc.get_reg_value('MXCSR') >> 13) & 0b11


def getftop(name):
    assert (name == 'ftop')
    return ((idc.get_reg_value('STAT') >> 11) & 0b111) - 8


def getfpu_tags(name):
    assert (name == 'fptag')
    re = 0
    tag = idc.get_reg_value('TAGS')
    for i in range(8):
        f = (0 if ((tag >> (2 * i)) & 0b11) else 1) << (8 * i)
        re = (re) | f

    return re


def get_fpu_regs(name):
    global rv
    assert (idaapi.is_reg_float(name))
    rv = idaapi.regval_t()
    rv.clear()
    if idaapi.get_reg_val(name, rv):
        ptr = int(rv.get_data())
        data = ctypes.cast(ptr, ctypes.POINTER(ctypes.c_uint8))
        re = []
        f80 = 0
        for i in range(2, 12):
            b8 = data[i]
            re.append(b8)
            f80 = f80 | (b8 << (8 * i))
        f64 = 0
        f64_l = convert_f80le_to_f64le(re)
        for i in range(8):
            f64 = (f64 << 8) | f64_l[7 - i]
        return [f80, f64]
    raise ('fk names')


def get_ymm(name):
    rv = idaapi.regval_t()
    if idaapi.get_reg_val(name, rv):
        return          int(rv.bytes()[::-1].hex(), 16)
    raise ('fk names')
    



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

# xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx


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


def FOA2VA(FOA):
    global dump_class_obj
    if not dump_class_obj:
        printf("mem dump is not init try shift - 2 ?")
        return None
        
    for segstr in dump_class_obj.mem_mmap:
        address, prd, length = dump_class_obj.mem_mmap[segstr]
        if (FOA >= prd and FOA <= length + prd):
            return FOA - prd + address
    return None

class ArchInfo:
    def __init__(self, ks_arch, register_names, registers):
        self.ks_arch = ks_arch
        self.register_names = register_names
        self.registers = registers
        

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
            arch = ArchInfo( keystone.KS_ARCH_X86,
                {0x10: 'rax', 0x18: 'rcx', 0x20: 'rdx', 0x28: 'rbx', 0x30: 'rsp', 0x38: 'rbp', 0x40: 'rsi', 0x48: 'rdi', 0x50: 'r8', 0x58: 'r9', 0x60: 'r10', 0x68: 'r11', 0x70: 'r12', 0x78: 'r13', 0x80: 'r14', 0x88: 'r15', 0x90: 'cc_op', 0x98: 'cc_dep1', 0xa0: 'cc_dep2', 0xa8: 'cc_ndep', 0xb0: 'd', 0xb8: 'rip', 0xc0: 'ac', 0xc8: 'id', 0xd0: 'fs', 0xd8: 'sseround', 0xe0: 'ymm0', 0x100: 'ymm1', 0x120: 'ymm2', 0x140: 'ymm3', 0x160: 'ymm4', 0x180: 'ymm5', 0x1a0: 'ymm6', 0x1c0: 'ymm7', 0x1e0: 'ymm8', 0x200: 'ymm9', 0x220: 'ymm10', 0x240: 'ymm11', 0x260: 'ymm12', 0x280: 'ymm13', 0x2a0: 'ymm14', 0x2c0: 'ymm15', 0x2e0: 'ymm16', 0x300: 'ftop', 0x308: 'fpreg', 0x348: 'fptag', 0x350: 'fpround', 0x358: 'fc3210', 0x360: 'emnote', 0x368: 'cmstart', 0x370: 'cmlen', 0x378: 'nraddr', 0x388: 'gs', 0x390: 'ip_at_syscall'},
                {'rax': (0x10, 0x8), 'eax': (0x10, 0x4), 'ax': (0x10, 0x2), 'al': (0x10, 0x1), 'ah': (0x11, 0x1), 'rcx': (0x18, 0x8), 'ecx': (0x18, 0x4), 'cx': (0x18, 0x2), 'cl': (0x18, 0x1), 'ch': (0x19, 0x1), 'rdx': (0x20, 0x8), 'edx': (0x20, 0x4), 'dx': (0x20, 0x2), 'dl': (0x20, 0x1), 'dh': (0x21, 0x1), 'rbx': (0x28, 0x8), 'ebx': (0x28, 0x4), 'bx': (0x28, 0x2), 'bl': (0x28, 0x1), 'bh': (0x29, 0x1), 'rsp': (0x30, 0x8), 'sp': (0x30, 0x8), 'esp': (0x30, 0x4), 'rbp': (0x38, 0x8), 'bp': (0x38, 0x8), 'ebp': (0x38, 0x4), 'rsi': (0x40, 0x8), 'esi': (0x40, 0x4), 'si': (0x40, 0x2), 'sil': (0x40, 0x1), 'sih': (0x41, 0x1), 'rdi': (0x48, 0x8), 'edi': (0x48, 0x4), 'di': (0x48, 0x2), 'dil': (0x48, 0x1), 'dih': (0x49, 0x1), 'r8': (0x50, 0x8), 'r9': (0x58, 0x8), 'r10': (0x60, 0x8), 'r11': (0x68, 0x8), 'r12': (0x70, 0x8), 'r13': (0x78, 0x8), 'r14': (0x80, 0x8), 'r15': (0x88, 0x8), 'cc_op': (0x90, 0x8), 'cc_dep1': (0x98, 0x8), 'cc_dep2': (0xa0, 0x8), 'cc_ndep': (0xa8, 0x8), 'd': (0xb0, 0x8), 'dflag': (0xb0, 0x8), 'rip': (0xb8, 0x8), 'ip': (0xb8, 0x8), 'pc': (0xb8, 0x8), 'ac': (0xc0, 0x8), 'acflag': (0xc0, 0x8), 'id': (0xc8, 0x8), 'idflag': (0xc8, 0x8), 'fs': (0xd0, 0x8), 'fs_const': (0xd0, 0x8), 'sseround': (0xd8, 0x8), 'ymm0': (0xe0, 0x20), 'xmm0': (0xe0, 0x10), 'ymm1': (0x100, 0x20), 'xmm1': (0x100, 0x10), 'ymm2': (0x120, 0x20), 'xmm2': (0x120, 0x10), 'ymm3': (0x140, 0x20), 'xmm3': (0x140, 0x10), 'ymm4': (0x160, 0x20), 'xmm4': (0x160, 0x10), 'ymm5': (0x180, 0x20), 'xmm5': (0x180, 0x10), 'ymm6': (0x1a0, 0x20), 'xmm6': (0x1a0, 0x10), 'ymm7': (0x1c0, 0x20), 'xmm7': (0x1c0, 0x10), 'ymm8': (0x1e0, 0x20), 'xmm8': (0x1e0, 0x10), 'ymm9': (0x200, 0x20), 'xmm9': (0x200, 0x10), 'ymm10': (0x220, 0x20), 'xmm10': (0x220, 0x10), 'ymm11': (0x240, 0x20), 'xmm11': (0x240, 0x10), 'ymm12': (0x260, 0x20), 'xmm12': (0x260, 0x10), 'ymm13': (0x280, 0x20), 'xmm13': (0x280, 0x10), 'ymm14': (0x2a0, 0x20), 'xmm14': (0x2a0, 0x10), 'ymm15': (0x2c0, 0x20), 'xmm15': (0x2c0, 0x10), 'ymm16': (0x2e0, 0x20), 'xmm16': (0x2e0, 0x10), 'ftop': (0x300, 0x4), 'fpreg': (0x308, 0x40), 'fpu_regs': (0x308, 0x40), 'mm0': (0x308, 0x8), 'mm1': (0x310, 0x8), 'mm2': (0x318, 0x8), 'mm3': (0x320, 0x8), 'mm4': (0x328, 0x8), 'mm5': (0x330, 0x8), 'mm6': (0x338, 0x8), 'mm7': (0x340, 0x8), 'fptag': (0x348, 0x8), 'fpu_tags': (0x348, 0x8), 'fpround': (0x350, 0x8), 'fc3210': (0x358, 0x8), 'emnote': (0x360, 0x4), 'cmstart': (0x368, 0x8), 'cmlen': (0x370, 0x8), 'nraddr': (0x378, 0x8), 'gs': (0x388, 0x8), 'gs_const': (0x388, 0x8), 'ip_at_syscall': (0x390, 0x8)}
            )
            mode = keystone.KS_MODE_64
            dumper = AMD64_dump(arch, mode)
        elif info.is_32bit():
            #arch = archinfo.ArchX86()
            arch = ArchInfo(keystone.KS_ARCH_X86,
                {8: 'eax', 12: 'ecx', 16: 'edx', 20: 'ebx', 24: 'esp', 28: 'ebp', 32: 'esi', 36: 'edi', 40: 'cc_op', 44: 'cc_dep1', 48: 'cc_dep2', 52: 'cc_ndep', 56: 'd', 60: 'id', 64: 'ac', 68: 'eip', 72: 'fpreg', 136: 'fptag', 144: 'fpround', 148: 'fc3210', 152: 'ftop', 156: 'sseround', 160: 'xmm0', 176: 'xmm1', 192: 'xmm2', 208: 'xmm3', 224: 'xmm4', 240: 'xmm5', 256: 'xmm6', 272: 'xmm7', 288: 'cs', 290: 'ds', 292: 'es', 294: 'fs', 296: 'gs', 298: 'ss', 304: 'ldt', 312: 'gdt', 320: 'emnote', 324: 'cmstart', 328: 'cmlen', 332: 'nraddr', 336: 'sc_class', 340: 'ip_at_syscall'} ,
                {'eax': (8, 4), 'ax': (8, 2), 'al': (8, 1), 'ah': (9, 1), 'ecx': (12, 4), 'cx': (12, 2), 'cl': (12, 1), 'ch': (13, 1), 'edx': (16, 4), 'dx': (16, 2), 'dl': (16, 1), 'dh': (17, 1), 'ebx': (20, 4), 'bx': (20, 2), 'bl': (20, 1), 'bh': (21, 1), 'esp': (24, 4), 'sp': (24, 4), 'ebp': (28, 4), 'bp': (28, 4), 'esi': (32, 4), 'si': (32, 2), 'sil': (32, 1), 'sih': (33, 1), 'edi': (36, 4), 'di': (36, 2), 'dil': (36, 1), 'dih': (37, 1), 'cc_op': (40, 4), 'cc_dep1': (44, 4), 'cc_dep2': (48, 4), 'cc_ndep': (52, 4), 'd': (56, 4), 'dflag': (56, 4), 'id': (60, 4), 'idflag': (60, 4), 'ac': (64, 4), 'acflag': (64, 4), 'eip': (68, 4), 'ip': (68, 4), 'pc': (68, 4), 'fpreg': (72, 64), 'fpu_regs': (72, 64), 'mm0': (72, 8), 'mm1': (80, 8), 'mm2': (88, 8), 'mm3': (96, 8), 'mm4': (104, 8), 'mm5': (112, 8), 'mm6': (120, 8), 'mm7': (128, 8), 'fptag': (136, 8), 'fpu_tags': (136, 8), 'fpround': (144, 4), 'fc3210': (148, 4), 'ftop': (152, 4), 'sseround': (156, 4), 'xmm0': (160, 16), 'xmm1': (176, 16), 'xmm2': (192, 16), 'xmm3': (208, 16), 'xmm4': (224, 16), 'xmm5': (240, 16), 'xmm6': (256, 16), 'xmm7': (272, 16), 'cs': (288, 2), 'ds': (290, 2), 'es': (292, 2), 'fs': (294, 2), 'gs': (296, 2), 'ss': (298, 2), 'ldt': (304, 8), 'gdt': (312, 8), 'emnote': (320, 4), 'cmstart': (324, 4), 'cmlen': (328, 4), 'nraddr': (332, 4), 'sc_class': (336, 4), 'ip_at_syscall': (340, 4)} )
            mode = keystone.KS_MODE_32
            dumper = X86_dump(arch, mode)
        else:
            #arch = archinfo.ArchNotFound()
            arch = ArchInfo(keystone.KS_ARCH_X86, {}, {})
            mode = keystone.KS_MODE_16

    elif cpuname.startswith("ppc"):
        if info.is_64bit():
            # arch = archinfo.ArchPPC64()
            arch = ArchInfo(keystone.KS_ARCH_PPC,
                {16: 'gpr0', 24: 'gpr1', 32: 'gpr2', 40: 'gpr3', 48: 'gpr4', 56: 'gpr5', 64: 'gpr6', 72: 'gpr7', 80: 'gpr8', 88: 'gpr9', 96: 'gpr10', 104: 'gpr11', 112: 'gpr12', 120: 'gpr13', 128: 'gpr14', 136: 'gpr15', 144: 'gpr16', 152: 'gpr17', 160: 'gpr18', 168: 'gpr19', 176: 'gpr20', 184: 'gpr21', 192: 'gpr22', 200: 'gpr23', 208: 'gpr24', 216: 'gpr25', 224: 'gpr26', 232: 'gpr27', 240: 'gpr28', 248: 'gpr29', 256: 'gpr30', 264: 'gpr31', 272: 'vsr0', 288: 'vsr1', 304: 'vsr2', 320: 'vsr3', 336: 'vsr4', 352: 'vsr5', 368: 'vsr6', 384: 'vsr7', 400: 'vsr8', 416: 'vsr9', 432: 'vsr10', 448: 'vsr11', 464: 'vsr12', 480: 'vsr13', 496: 'vsr14', 512: 'vsr15', 528: 'vsr16', 544: 'vsr17', 560: 'vsr18', 576: 'vsr19', 592: 'vsr20', 608: 'vsr21', 624: 'vsr22', 640: 'vsr23', 656: 'vsr24', 672: 'vsr25', 688: 'vsr26', 704: 'vsr27', 720: 'vsr28', 736: 'vsr29', 752: 'vsr30', 768: 'vsr31', 784: 'vsr32', 800: 'vsr33', 816: 'vsr34', 832: 'vsr35', 848: 'vsr36', 864: 'vsr37', 880: 'vsr38', 896: 'vsr39', 912: 'vsr40', 928: 'vsr41', 944: 'vsr42', 960: 'vsr43', 976: 'vsr44', 992: 'vsr45', 1008: 'vsr46', 1024: 'vsr47', 1040: 'vsr48', 1056: 'vsr49', 1072: 'vsr50', 1088: 'vsr51', 1104: 'vsr52', 1120: 'vsr53', 1136: 'vsr54', 1152: 'vsr55', 1168: 'vsr56', 1184: 'vsr57', 1200: 'vsr58', 1216: 'vsr59', 1232: 'vsr60', 1248: 'vsr61', 1264: 'vsr62', 1280: 'vsr63', 1296: 'cia', 1304: 'lr', 1312: 'ctr', 1320: 'xer_so', 1321: 'xer_ov', 1322: 'xer_ca', 1323: 'xer_bc', 1324: 'cr0_321', 1325: 'cr0_0', 1326: 'cr1_321', 1327: 'cr1_0', 1328: 'cr2_321', 1329: 'cr2_0', 1330: 'cr3_321', 1331: 'cr3_0', 1332: 'cr4_321', 1333: 'cr4_0', 1334: 'cr5_321', 1335: 'cr5_0', 1336: 'cr6_321', 1337: 'cr6_0', 1338: 'cr7_321', 1339: 'cr7_0', 1340: 'fpround', 1341: 'dfpround', 1342: 'c_fpcc', 1344: 'vrsave', 1348: 'vscr', 1352: 'emnote', 1360: 'cmstart', 1368: 'cmlen', 1376: 'nraddr', 1384: 'nraddr_gpr2', 1392: 'redir_sp', 1400: 'redir_stack', 1656: 'ip_at_syscall', 1664: 'sprg3_ro', 1672: 'tfhar', 1680: 'texasr', 1688: 'tfiar', 1696: 'ppr', 1704: 'texasru', 1708: 'pspb'} ,
                {'gpr0': (16, 8), 'r0': (16, 8), 'gpr1': (24, 8), 'r1': (24, 8), 'sp': (24, 8), 'gpr2': (32, 8), 'r2': (32, 8), 'rtoc': (32, 8), 'gpr3': (40, 8), 'r3': (40, 8), 'gpr4': (48, 8), 'r4': (48, 8), 'gpr5': (56, 8), 'r5': (56, 8), 'gpr6': (64, 8), 'r6': (64, 8), 'gpr7': (72, 8), 'r7': (72, 8), 'gpr8': (80, 8), 'r8': (80, 8), 'gpr9': (88, 8), 'r9': (88, 8), 'gpr10': (96, 8), 'r10': (96, 8), 'gpr11': (104, 8), 'r11': (104, 8), 'gpr12': (112, 8), 'r12': (112, 8), 'gpr13': (120, 8), 'r13': (120, 8), 'gpr14': (128, 8), 'r14': (128, 8), 'gpr15': (136, 8), 'r15': (136, 8), 'gpr16': (144, 8), 'r16': (144, 8), 'gpr17': (152, 8), 'r17': (152, 8), 'gpr18': (160, 8), 'r18': (160, 8), 'gpr19': (168, 8), 'r19': (168, 8), 'gpr20': (176, 8), 'r20': (176, 8), 'gpr21': (184, 8), 'r21': (184, 8), 'gpr22': (192, 8), 'r22': (192, 8), 'gpr23': (200, 8), 'r23': (200, 8), 'gpr24': (208, 8), 'r24': (208, 8), 'gpr25': (216, 8), 'r25': (216, 8), 'gpr26': (224, 8), 'r26': (224, 8), 'gpr27': (232, 8), 'r27': (232, 8), 'gpr28': (240, 8), 'r28': (240, 8), 'gpr29': (248, 8), 'r29': (248, 8), 'gpr30': (256, 8), 'r30': (256, 8), 'gpr31': (264, 8), 'r31': (264, 8), 'bp': (264, 8), 'vsr0': (272, 16), 'v0': (272, 16), 'fpr0': (272, 8), 'vsr1': (288, 16), 'v1': (288, 16), 'fpr1': (288, 8), 'vsr2': (304, 16), 'v2': (304, 16), 'fpr2': (304, 8), 'vsr3': (320, 16), 'v3': (320, 16), 'fpr3': (320, 8), 'vsr4': (336, 16), 'v4': (336, 16), 'fpr4': (336, 8), 'vsr5': (352, 16), 'v5': (352, 16), 'fpr5': (352, 8), 'vsr6': (368, 16), 'v6': (368, 16), 'fpr6': (368, 8), 'vsr7': (384, 16), 'v7': (384, 16), 'fpr7': (384, 8), 'vsr8': (400, 16), 'v8': (400, 16), 'fpr8': (400, 8), 'vsr9': (416, 16), 'v9': (416, 16), 'fpr9': (416, 8), 'vsr10': (432, 16), 'v10': (432, 16), 'fpr10': (432, 8), 'vsr11': (448, 16), 'v11': (448, 16), 'fpr11': (448, 8), 'vsr12': (464, 16), 'v12': (464, 16), 'fpr12': (464, 8), 'vsr13': (480, 16), 'v13': (480, 16), 'fpr13': (480, 8), 'vsr14': (496, 16), 'v14': (496, 16), 'fpr14': (496, 8), 'vsr15': (512, 16), 'v15': (512, 16), 'fpr15': (512, 8), 'vsr16': (528, 16), 'v16': (528, 16), 'fpr16': (528, 8), 'vsr17': (544, 16), 'v17': (544, 16), 'fpr17': (544, 8), 'vsr18': (560, 16), 'v18': (560, 16), 'fpr18': (560, 8), 'vsr19': (576, 16), 'v19': (576, 16), 'fpr19': (576, 8), 'vsr20': (592, 16), 'v20': (592, 16), 'fpr20': (592, 8), 'vsr21': (608, 16), 'v21': (608, 16), 'fpr21': (608, 8), 'vsr22': (624, 16), 'v22': (624, 16), 'fpr22': (624, 8), 'vsr23': (640, 16), 'v23': (640, 16), 'fpr23': (640, 8), 'vsr24': (656, 16), 'v24': (656, 16), 'fpr24': (656, 8), 'vsr25': (672, 16), 'v25': (672, 16), 'fpr25': (672, 8), 'vsr26': (688, 16), 'v26': (688, 16), 'fpr26': (688, 8), 'vsr27': (704, 16), 'v27': (704, 16), 'fpr27': (704, 8), 'vsr28': (720, 16), 'v28': (720, 16), 'fpr28': (720, 8), 'vsr29': (736, 16), 'v29': (736, 16), 'fpr29': (736, 8), 'vsr30': (752, 16), 'v30': (752, 16), 'fpr30': (752, 8), 'vsr31': (768, 16), 'v31': (768, 16), 'fpr31': (768, 8), 'vsr32': (784, 16), 'v32': (784, 16), 'vsr33': (800, 16), 'v33': (800, 16), 'vsr34': (816, 16), 'v34': (816, 16), 'vsr35': (832, 16), 'v35': (832, 16), 'vsr36': (848, 16), 'v36': (848, 16), 'vsr37': (864, 16), 'v37': (864, 16), 'vsr38': (880, 16), 'v38': (880, 16), 'vsr39': (896, 16), 'v39': (896, 16), 'vsr40': (912, 16), 'v40': (912, 16), 'vsr41': (928, 16), 'v41': (928, 16), 'vsr42': (944, 16), 'v42': (944, 16), 'vsr43': (960, 16), 'v43': (960, 16), 'vsr44': (976, 16), 'v44': (976, 16), 'vsr45': (992, 16), 'v45': (992, 16), 'vsr46': (1008, 16), 'v46': (1008, 16), 'vsr47': (1024, 16), 'v47': (1024, 16), 'vsr48': (1040, 16), 'v48': (1040, 16), 'vsr49': (1056, 16), 'v49': (1056, 16), 'vsr50': (1072, 16), 'v50': (1072, 16), 'vsr51': (1088, 16), 'v51': (1088, 16), 'vsr52': (1104, 16), 'v52': (1104, 16), 'vsr53': (1120, 16), 'v53': (1120, 16), 'vsr54': (1136, 16), 'v54': (1136, 16), 'vsr55': (1152, 16), 'v55': (1152, 16), 'vsr56': (1168, 16), 'v56': (1168, 16), 'vsr57': (1184, 16), 'v57': (1184, 16), 'vsr58': (1200, 16), 'v58': (1200, 16), 'vsr59': (1216, 16), 'v59': (1216, 16), 'vsr60': (1232, 16), 'v60': (1232, 16), 'vsr61': (1248, 16), 'v61': (1248, 16), 'vsr62': (1264, 16), 'v62': (1264, 16), 'vsr63': (1280, 16), 'v63': (1280, 16), 'cia': (1296, 8), 'ip': (1296, 8), 'pc': (1296, 8), 'lr': (1304, 8), 'ctr': (1312, 8), 'xer_so': (1320, 1), 'xer_ov': (1321, 1), 'xer_ca': (1322, 1), 'xer_bc': (1323, 1), 'cr0_321': (1324, 1), 'cr0_0': (1325, 1), 'cr0': (1325, 1), 'cr1_321': (1326, 1), 'cr1_0': (1327, 1), 'cr1': (1327, 1), 'cr2_321': (1328, 1), 'cr2_0': (1329, 1), 'cr2': (1329, 1), 'cr3_321': (1330, 1), 'cr3_0': (1331, 1), 'cr3': (1331, 1), 'cr4_321': (1332, 1), 'cr4_0': (1333, 1), 'cr4': (1333, 1), 'cr5_321': (1334, 1), 'cr5_0': (1335, 1), 'cr5': (1335, 1), 'cr6_321': (1336, 1), 'cr6_0': (1337, 1), 'cr6': (1337, 1), 'cr7_321': (1338, 1), 'cr7_0': (1339, 1), 'cr7': (1339, 1), 'fpround': (1340, 1), 'dfpround': (1341, 1), 'c_fpcc': (1342, 1), 'vrsave': (1344, 4), 'vscr': (1348, 4), 'emnote': (1352, 4), 'cmstart': (1360, 8), 'cmlen': (1368, 8), 'nraddr': (1376, 8), 'nraddr_gpr2': (1384, 8), 'redir_sp': (1392, 8), 'redir_stack': (1400, 256), 'ip_at_syscall': (1656, 8), 'sprg3_ro': (1664, 8), 'tfhar': (1672, 8), 'texasr': (1680, 8), 'tfiar': (1688, 8), 'ppr': (1696, 8), 'texasru': (1704, 4), 'pspb': (1708, 4)} )
            mode = keystone.KS_MODE_PPC64
        else:
            # arch = archinfo.ArchPPC32()
            arch = ArchInfo(keystone.KS_ARCH_PPC,
                {16: 'gpr0', 20: 'gpr1', 24: 'gpr2', 28: 'gpr3', 32: 'gpr4', 36: 'gpr5', 40: 'gpr6', 44: 'gpr7', 48: 'gpr8', 52: 'gpr9', 56: 'gpr10', 60: 'gpr11', 64: 'gpr12', 68: 'gpr13', 72: 'gpr14', 76: 'gpr15', 80: 'gpr16', 84: 'gpr17', 88: 'gpr18', 92: 'gpr19', 96: 'gpr20', 100: 'gpr21', 104: 'gpr22', 108: 'gpr23', 112: 'gpr24', 116: 'gpr25', 120: 'gpr26', 124: 'gpr27', 128: 'gpr28', 132: 'gpr29', 136: 'gpr30', 140: 'gpr31', 144: 'vsr0', 160: 'vsr1', 176: 'vsr2', 192: 'vsr3', 208: 'vsr4', 224: 'vsr5', 240: 'vsr6', 256: 'vsr7', 272: 'vsr8', 288: 'vsr9', 304: 'vsr10', 320: 'vsr11', 336: 'vsr12', 352: 'vsr13', 368: 'vsr14', 384: 'vsr15', 400: 'vsr16', 416: 'vsr17', 432: 'vsr18', 448: 'vsr19', 464: 'vsr20', 480: 'vsr21', 496: 'vsr22', 512: 'vsr23', 528: 'vsr24', 544: 'vsr25', 560: 'vsr26', 576: 'vsr27', 592: 'vsr28', 608: 'vsr29', 624: 'vsr30', 640: 'vsr31', 656: 'vsr32', 672: 'vsr33', 688: 'vsr34', 704: 'vsr35', 720: 'vsr36', 736: 'vsr37', 752: 'vsr38', 768: 'vsr39', 784: 'vsr40', 800: 'vsr41', 816: 'vsr42', 832: 'vsr43', 848: 'vsr44', 864: 'vsr45', 880: 'vsr46', 896: 'vsr47', 912: 'vsr48', 928: 'vsr49', 944: 'vsr50', 960: 'vsr51', 976: 'vsr52', 992: 'vsr53', 1008: 'vsr54', 1024: 'vsr55', 1040: 'vsr56', 1056: 'vsr57', 1072: 'vsr58', 1088: 'vsr59', 1104: 'vsr60', 1120: 'vsr61', 1136: 'vsr62', 1152: 'vsr63', 1168: 'cia', 1172: 'lr', 1176: 'ctr', 1180: 'xer_so', 1181: 'xer_ov', 1182: 'xer_ca', 1183: 'xer_bc', 1184: 'cr0_321', 1185: 'cr0_0', 1186: 'cr1_321', 1187: 'cr1_0', 1188: 'cr2_321', 1189: 'cr2_0', 1190: 'cr3_321', 1191: 'cr3_0', 1192: 'cr4_321', 1193: 'cr4_0', 1194: 'cr5_321', 1195: 'cr5_0', 1196: 'cr6_321', 1197: 'cr6_0', 1198: 'cr7_321', 1199: 'cr7_0', 1200: 'fpround', 1201: 'dfpround', 1202: 'c_fpcc', 1204: 'vrsave', 1208: 'vscr', 1212: 'emnote', 1216: 'cmstart', 1220: 'cmlen', 1224: 'nraddr', 1228: 'nraddr_gpr2', 1232: 'redir_sp', 1236: 'redir_stack', 1364: 'ip_at_syscall', 1368: 'sprg3_ro', 1376: 'tfhar', 1384: 'texasr', 1392: 'tfiar', 1400: 'ppr', 1408: 'texasru', 1412: 'pspb'} ,
                {'gpr0': (16, 4), 'r0': (16, 4), 'gpr1': (20, 4), 'r1': (20, 4), 'sp': (20, 4), 'gpr2': (24, 4), 'r2': (24, 4), 'gpr3': (28, 4), 'r3': (28, 4), 'gpr4': (32, 4), 'r4': (32, 4), 'gpr5': (36, 4), 'r5': (36, 4), 'gpr6': (40, 4), 'r6': (40, 4), 'gpr7': (44, 4), 'r7': (44, 4), 'gpr8': (48, 4), 'r8': (48, 4), 'gpr9': (52, 4), 'r9': (52, 4), 'gpr10': (56, 4), 'r10': (56, 4), 'gpr11': (60, 4), 'r11': (60, 4), 'gpr12': (64, 4), 'r12': (64, 4), 'gpr13': (68, 4), 'r13': (68, 4), 'gpr14': (72, 4), 'r14': (72, 4), 'gpr15': (76, 4), 'r15': (76, 4), 'gpr16': (80, 4), 'r16': (80, 4), 'gpr17': (84, 4), 'r17': (84, 4), 'gpr18': (88, 4), 'r18': (88, 4), 'gpr19': (92, 4), 'r19': (92, 4), 'gpr20': (96, 4), 'r20': (96, 4), 'gpr21': (100, 4), 'r21': (100, 4), 'gpr22': (104, 4), 'r22': (104, 4), 'gpr23': (108, 4), 'r23': (108, 4), 'gpr24': (112, 4), 'r24': (112, 4), 'gpr25': (116, 4), 'r25': (116, 4), 'gpr26': (120, 4), 'r26': (120, 4), 'gpr27': (124, 4), 'r27': (124, 4), 'gpr28': (128, 4), 'r28': (128, 4), 'gpr29': (132, 4), 'r29': (132, 4), 'gpr30': (136, 4), 'r30': (136, 4), 'gpr31': (140, 4), 'r31': (140, 4), 'bp': (140, 4), 'vsr0': (144, 16), 'v0': (144, 16), 'fpr0': (144, 8), 'vsr1': (160, 16), 'v1': (160, 16), 'fpr1': (160, 8), 'vsr2': (176, 16), 'v2': (176, 16), 'fpr2': (176, 8), 'vsr3': (192, 16), 'v3': (192, 16), 'fpr3': (192, 8), 'vsr4': (208, 16), 'v4': (208, 16), 'fpr4': (208, 8), 'vsr5': (224, 16), 'v5': (224, 16), 'fpr5': (224, 8), 'vsr6': (240, 16), 'v6': (240, 16), 'fpr6': (240, 8), 'vsr7': (256, 16), 'v7': (256, 16), 'fpr7': (256, 8), 'vsr8': (272, 16), 'v8': (272, 16), 'fpr8': (272, 8), 'vsr9': (288, 16), 'v9': (288, 16), 'fpr9': (288, 8), 'vsr10': (304, 16), 'v10': (304, 16), 'fpr10': (304, 8), 'vsr11': (320, 16), 'v11': (320, 16), 'fpr11': (320, 8), 'vsr12': (336, 16), 'v12': (336, 16), 'fpr12': (336, 8), 'vsr13': (352, 16), 'v13': (352, 16), 'fpr13': (352, 8), 'vsr14': (368, 16), 'v14': (368, 16), 'fpr14': (368, 8), 'vsr15': (384, 16), 'v15': (384, 16), 'fpr15': (384, 8), 'vsr16': (400, 16), 'v16': (400, 16), 'fpr16': (400, 8), 'vsr17': (416, 16), 'v17': (416, 16), 'fpr17': (416, 8), 'vsr18': (432, 16), 'v18': (432, 16), 'fpr18': (432, 8), 'vsr19': (448, 16), 'v19': (448, 16), 'fpr19': (448, 8), 'vsr20': (464, 16), 'v20': (464, 16), 'fpr20': (464, 8), 'vsr21': (480, 16), 'v21': (480, 16), 'fpr21': (480, 8), 'vsr22': (496, 16), 'v22': (496, 16), 'fpr22': (496, 8), 'vsr23': (512, 16), 'v23': (512, 16), 'fpr23': (512, 8), 'vsr24': (528, 16), 'v24': (528, 16), 'fpr24': (528, 8), 'vsr25': (544, 16), 'v25': (544, 16), 'fpr25': (544, 8), 'vsr26': (560, 16), 'v26': (560, 16), 'fpr26': (560, 8), 'vsr27': (576, 16), 'v27': (576, 16), 'fpr27': (576, 8), 'vsr28': (592, 16), 'v28': (592, 16), 'fpr28': (592, 8), 'vsr29': (608, 16), 'v29': (608, 16), 'fpr29': (608, 8), 'vsr30': (624, 16), 'v30': (624, 16), 'fpr30': (624, 8), 'vsr31': (640, 16), 'v31': (640, 16), 'fpr31': (640, 8), 'vsr32': (656, 16), 'v32': (656, 16), 'vsr33': (672, 16), 'v33': (672, 16), 'vsr34': (688, 16), 'v34': (688, 16), 'vsr35': (704, 16), 'v35': (704, 16), 'vsr36': (720, 16), 'v36': (720, 16), 'vsr37': (736, 16), 'v37': (736, 16), 'vsr38': (752, 16), 'v38': (752, 16), 'vsr39': (768, 16), 'v39': (768, 16), 'vsr40': (784, 16), 'v40': (784, 16), 'vsr41': (800, 16), 'v41': (800, 16), 'vsr42': (816, 16), 'v42': (816, 16), 'vsr43': (832, 16), 'v43': (832, 16), 'vsr44': (848, 16), 'v44': (848, 16), 'vsr45': (864, 16), 'v45': (864, 16), 'vsr46': (880, 16), 'v46': (880, 16), 'vsr47': (896, 16), 'v47': (896, 16), 'vsr48': (912, 16), 'v48': (912, 16), 'vsr49': (928, 16), 'v49': (928, 16), 'vsr50': (944, 16), 'v50': (944, 16), 'vsr51': (960, 16), 'v51': (960, 16), 'vsr52': (976, 16), 'v52': (976, 16), 'vsr53': (992, 16), 'v53': (992, 16), 'vsr54': (1008, 16), 'v54': (1008, 16), 'vsr55': (1024, 16), 'v55': (1024, 16), 'vsr56': (1040, 16), 'v56': (1040, 16), 'vsr57': (1056, 16), 'v57': (1056, 16), 'vsr58': (1072, 16), 'v58': (1072, 16), 'vsr59': (1088, 16), 'v59': (1088, 16), 'vsr60': (1104, 16), 'v60': (1104, 16), 'vsr61': (1120, 16), 'v61': (1120, 16), 'vsr62': (1136, 16), 'v62': (1136, 16), 'vsr63': (1152, 16), 'v63': (1152, 16), 'cia': (1168, 4), 'ip': (1168, 4), 'pc': (1168, 4), 'lr': (1172, 4), 'ctr': (1176, 4), 'xer_so': (1180, 1), 'xer_ov': (1181, 1), 'xer_ca': (1182, 1), 'xer_bc': (1183, 1), 'cr0_321': (1184, 1), 'cr0_0': (1185, 1), 'cr0': (1185, 1), 'cr1_321': (1186, 1), 'cr1_0': (1187, 1), 'cr1': (1187, 1), 'cr2_321': (1188, 1), 'cr2_0': (1189, 1), 'cr2': (1189, 1), 'cr3_321': (1190, 1), 'cr3_0': (1191, 1), 'cr3': (1191, 1), 'cr4_321': (1192, 1), 'cr4_0': (1193, 1), 'cr4': (1193, 1), 'cr5_321': (1194, 1), 'cr5_0': (1195, 1), 'cr5': (1195, 1), 'cr6_321': (1196, 1), 'cr6_0': (1197, 1), 'cr6': (1197, 1), 'cr7_321': (1198, 1), 'cr7_0': (1199, 1), 'cr7': (1199, 1), 'fpround': (1200, 1), 'dfpround': (1201, 1), 'c_fpcc': (1202, 1), 'vrsave': (1204, 4), 'vscr': (1208, 4), 'emnote': (1212, 4), 'cmstart': (1216, 4), 'cmlen': (1220, 4), 'nraddr': (1224, 4), 'nraddr_gpr2': (1228, 4), 'redir_sp': (1232, 4), 'redir_stack': (1236, 128), 'ip_at_syscall': (1364, 4), 'sprg3_ro': (1368, 4), 'tfhar': (1376, 8), 'texasr': (1384, 8), 'tfiar': (1392, 8), 'ppr': (1400, 8), 'texasru': (1408, 4), 'pspb': (1412, 4)} )
            mode = keystone.KS_MODE_PPC32
        if cpuname == "ppc":
            # do not support Little Endian mode for PPC
            mode += keystone.KS_MODE_BIG_ENDIAN

    elif cpuname.startswith("mips"):
        if info.is_64bit():
            # arch = archinfo.ArchMIPS64()
            arch = ArchInfo(keystone.KS_ARCH_MIPS, 
                {16: 'zero', 24: 'at', 32: 'v0', 40: 'v1', 48: 'a0', 56: 'a1', 64: 'a2', 72: 'a3', 80: 't0', 88: 't1', 96: 't2', 104: 't3', 112: 't4', 120: 't5', 128: 't6', 136: 't7', 144: 's0', 152: 's1', 160: 's2', 168: 's3', 176: 's4', 184: 's5', 192: 's6', 200: 's7', 208: 't8', 216: 't9', 224: 'k0', 232: 'k1', 240: 'gp', 248: 'sp', 256: 's8', 264: 'ra', 272: 'pc', 280: 'hi', 288: 'lo', 296: 'f0', 304: 'f1', 312: 'f2', 320: 'f3', 328: 'f4', 336: 'f5', 344: 'f6', 352: 'f7', 360: 'f8', 368: 'f9', 376: 'f10', 384: 'f11', 392: 'f12', 400: 'f13', 408: 'f14', 416: 'f15', 424: 'f16', 432: 'f17', 440: 'f18', 448: 'f19', 456: 'f20', 464: 'f21', 472: 'f22', 480: 'f23', 488: 'f24', 496: 'f25', 504: 'f26', 512: 'f27', 520: 'f28', 528: 'f29', 536: 'f30', 544: 'f31', 552: 'fir', 556: 'fccr', 560: 'fexr', 564: 'fenr', 568: 'fcsr', 572: 'cp0_status', 576: 'ulr', 584: 'emnote', 588: 'cond', 592: 'cmstart', 600: 'cmlen', 608: 'nraddr', 616: 'ip_at_syscall'} ,
                {'zero': (16, 8), 'r0': (16, 8), 'at': (24, 8), 'r1': (24, 8), 'v0': (32, 8), 'r2': (32, 8), 'v1': (40, 8), 'r3': (40, 8), 'a0': (48, 8), 'r4': (48, 8), 'a1': (56, 8), 'r5': (56, 8), 'a2': (64, 8), 'r6': (64, 8), 'a3': (72, 8), 'r7': (72, 8), 't0': (80, 8), 'r8': (80, 8), 't1': (88, 8), 'r9': (88, 8), 't2': (96, 8), 'r10': (96, 8), 't3': (104, 8), 'r11': (104, 8), 't4': (112, 8), 'r12': (112, 8), 't5': (120, 8), 'r13': (120, 8), 't6': (128, 8), 'r14': (128, 8), 't7': (136, 8), 'r15': (136, 8), 's0': (144, 8), 'r16': (144, 8), 's1': (152, 8), 'r17': (152, 8), 's2': (160, 8), 'r18': (160, 8), 's3': (168, 8), 'r19': (168, 8), 's4': (176, 8), 'r20': (176, 8), 's5': (184, 8), 'r21': (184, 8), 's6': (192, 8), 'r22': (192, 8), 's7': (200, 8), 'r23': (200, 8), 't8': (208, 8), 'r24': (208, 8), 't9': (216, 8), 'r25': (216, 8), 'k0': (224, 8), 'r26': (224, 8), 'k1': (232, 8), 'r27': (232, 8), 'gp': (240, 8), 'r28': (240, 8), 'sp': (248, 8), 'r29': (248, 8), 's8': (256, 8), 'r30': (256, 8), 'fp': (256, 8), 'bp': (256, 8), 'ra': (264, 8), 'r31': (264, 8), 'lr': (264, 8), 'pc': (272, 8), 'ip': (272, 8), 'hi': (280, 8), 'lo': (288, 8), 'f0': (296, 8), 'f1': (304, 8), 'f2': (312, 8), 'f3': (320, 8), 'f4': (328, 8), 'f5': (336, 8), 'f6': (344, 8), 'f7': (352, 8), 'f8': (360, 8), 'f9': (368, 8), 'f10': (376, 8), 'f11': (384, 8), 'f12': (392, 8), 'f13': (400, 8), 'f14': (408, 8), 'f15': (416, 8), 'f16': (424, 8), 'f17': (432, 8), 'f18': (440, 8), 'f19': (448, 8), 'f20': (456, 8), 'f21': (464, 8), 'f22': (472, 8), 'f23': (480, 8), 'f24': (488, 8), 'f25': (496, 8), 'f26': (504, 8), 'f27': (512, 8), 'f28': (520, 8), 'f29': (528, 8), 'f30': (536, 8), 'f31': (544, 8), 'fir': (552, 4), 'fccr': (556, 4), 'fexr': (560, 4), 'fenr': (564, 4), 'fcsr': (568, 4), 'cp0_status': (572, 4), 'ulr': (576, 8), 'emnote': (584, 4), 'cond': (588, 4), 'cmstart': (592, 8), 'cmlen': (600, 8), 'nraddr': (608, 8), 'ip_at_syscall': (616, 8)} )
            mode = keystone.KS_MODE_MIPS64
        else:
            # arch = archinfo.ArchMIPS32()
            arch = ArchInfo(keystone.KS_ARCH_MIPS, 
                {8: 'zero', 12: 'at', 16: 'v0', 20: 'v1', 24: 'a0', 28: 'a1', 32: 'a2', 36: 'a3', 40: 't0', 44: 't1', 48: 't2', 52: 't3', 56: 't4', 60: 't5', 64: 't6', 68: 't7', 72: 's0', 76: 's1', 80: 's2', 84: 's3', 88: 's4', 92: 's5', 96: 's6', 100: 's7', 104: 't8', 108: 't9', 112: 'k0', 116: 'k1', 120: 'gp', 124: 'sp', 128: 's8', 132: 'ra', 136: 'pc', 140: 'hi', 144: 'lo', 152: 'f0', 160: 'f1', 168: 'f2', 176: 'f3', 184: 'f4', 192: 'f5', 200: 'f6', 208: 'f7', 216: 'f8', 224: 'f9', 232: 'f10', 240: 'f11', 248: 'f12', 256: 'f13', 264: 'f14', 272: 'f15', 280: 'f16', 288: 'f17', 296: 'f18', 304: 'f19', 312: 'f20', 320: 'f21', 328: 'f22', 336: 'f23', 344: 'f24', 352: 'f25', 360: 'f26', 368: 'f27', 376: 'f28', 384: 'f29', 392: 'f30', 400: 'f31', 408: 'fir', 412: 'fccr', 416: 'fexr', 420: 'fenr', 424: 'fcsr', 428: 'ulr', 432: 'emnote', 436: 'cmstart', 440: 'cmlen', 444: 'nraddr', 448: 'cond', 452: 'dspcontrol', 456: 'ac0', 464: 'ac1', 472: 'ac2', 480: 'ac3', 488: 'cp0_status', 492: 'ip_at_syscall'} ,
                {'zero': (8, 4), 'r0': (8, 4), 'at': (12, 4), 'r1': (12, 4), 'v0': (16, 4), 'r2': (16, 4), 'v1': (20, 4), 'r3': (20, 4), 'a0': (24, 4), 'r4': (24, 4), 'a1': (28, 4), 'r5': (28, 4), 'a2': (32, 4), 'r6': (32, 4), 'a3': (36, 4), 'r7': (36, 4), 't0': (40, 4), 'r8': (40, 4), 't1': (44, 4), 'r9': (44, 4), 't2': (48, 4), 'r10': (48, 4), 't3': (52, 4), 'r11': (52, 4), 't4': (56, 4), 'r12': (56, 4), 't5': (60, 4), 'r13': (60, 4), 't6': (64, 4), 'r14': (64, 4), 't7': (68, 4), 'r15': (68, 4), 's0': (72, 4), 'r16': (72, 4), 's1': (76, 4), 'r17': (76, 4), 's2': (80, 4), 'r18': (80, 4), 's3': (84, 4), 'r19': (84, 4), 's4': (88, 4), 'r20': (88, 4), 's5': (92, 4), 'r21': (92, 4), 's6': (96, 4), 'r22': (96, 4), 's7': (100, 4), 'r23': (100, 4), 't8': (104, 4), 'r24': (104, 4), 't9': (108, 4), 'r25': (108, 4), 'k0': (112, 4), 'r26': (112, 4), 'k1': (116, 4), 'r27': (116, 4), 'gp': (120, 4), 'r28': (120, 4), 'sp': (124, 4), 'r29': (124, 4), 's8': (128, 4), 'r30': (128, 4), 'fp': (128, 4), 'bp': (128, 4), 'ra': (132, 4), 'r31': (132, 4), 'lr': (132, 4), 'pc': (136, 4), 'ip': (136, 4), 'hi': (140, 4), 'lo': (144, 4), 'f0': (152, 8), 'f1': (160, 8), 'f2': (168, 8), 'f3': (176, 8), 'f4': (184, 8), 'f5': (192, 8), 'f6': (200, 8), 'f7': (208, 8), 'f8': (216, 8), 'f9': (224, 8), 'f10': (232, 8), 'f11': (240, 8), 'f12': (248, 8), 'f13': (256, 8), 'f14': (264, 8), 'f15': (272, 8), 'f16': (280, 8), 'f17': (288, 8), 'f18': (296, 8), 'f19': (304, 8), 'f20': (312, 8), 'f21': (320, 8), 'f22': (328, 8), 'f23': (336, 8), 'f24': (344, 8), 'f25': (352, 8), 'f26': (360, 8), 'f27': (368, 8), 'f28': (376, 8), 'f29': (384, 8), 'f30': (392, 8), 'f31': (400, 8), 'fir': (408, 4), 'fccr': (412, 4), 'fexr': (416, 4), 'fenr': (420, 4), 'fcsr': (424, 4), 'ulr': (428, 4), 'emnote': (432, 4), 'cmstart': (436, 4), 'cmlen': (440, 4), 'nraddr': (444, 4), 'cond': (448, 4), 'dspcontrol': (452, 4), 'ac0': (456, 8), 'ac1': (464, 8), 'ac2': (472, 8), 'ac3': (480, 8), 'cp0_status': (488, 4), 'ip_at_syscall': (492, 4)} )
            mode = keystone.KS_MODE_MIPS32
    elif cpuname.startswith("systemz") or cpuname.startswith("s390x"):
        # arch = archinfo.ArchS390X()
        arch = ArchInfo(
            {336: 'ia', 192: 'r0', 200: 'r1', 208: 'r2', 216: 'r3', 224: 'r4', 232: 'r5', 240: 'r6', 248: 'r7', 256: 'r8', 264: 'r9', 272: 'r10', 280: 'r11', 288: 'r12', 296: 'r13', 304: 'r14', 312: 'r15', 64: 'f0', 72: 'f1', 80: 'f2', 88: 'f3', 96: 'f4', 104: 'f5', 112: 'f6', 120: 'f7', 128: 'f8', 136: 'f9', 144: 'f10', 152: 'f11', 160: 'f12', 168: 'f13', 176: 'f14', 184: 'f15', 0: 'a0', 4: 'a1', 8: 'a2', 12: 'a3', 16: 'a4', 20: 'a5', 24: 'a6', 28: 'a7', 32: 'a8', 36: 'a9', 40: 'a10', 44: 'a11', 48: 'a12', 52: 'a13', 56: 'a14', 60: 'a15', 384: 'nraddr', 392: 'cmstart', 400: 'cmlen', 408: 'ip_at_syscall', 416: 'emnote'} ,
            {'ia': (336, 8), 'ip': (336, 8), 'pc': (336, 8), 'r0': (192, 8), 'r1': (200, 8), 'r2': (208, 8), 'r3': (216, 8), 'r4': (224, 8), 'r5': (232, 8), 'r6': (240, 8), 'r7': (248, 8), 'r8': (256, 8), 'r9': (264, 8), 'r10': (272, 8), 'r11': (280, 8), 'bp': (280, 8), 'r12': (288, 8), 'r13': (296, 8), 'r14': (304, 8), 'r15': (312, 8), 'sp': (312, 8), 'f0': (64, 8), 'f1': (72, 8), 'f2': (80, 8), 'f3': (88, 8), 'f4': (96, 8), 'f5': (104, 8), 'f6': (112, 8), 'f7': (120, 8), 'f8': (128, 8), 'f9': (136, 8), 'f10': (144, 8), 'f11': (152, 8), 'f12': (160, 8), 'f13': (168, 8), 'f14': (176, 8), 'f15': (184, 8), 'a0': (0, 4), 'a1': (4, 4), 'a2': (8, 4), 'a3': (12, 4), 'a4': (16, 4), 'a5': (20, 4), 'a6': (24, 4), 'a7': (28, 4), 'a8': (32, 4), 'a9': (36, 4), 'a10': (40, 4), 'a11': (44, 4), 'a12': (48, 4), 'a13': (52, 4), 'a14': (56, 4), 'a15': (60, 4), 'nraddr': (384, 8), 'cmstart': (392, 8), 'cmlen': (400, 8), 'ip_at_syscall': (408, 8), 'emnote': (416, 4)} )
        mode = keystone.KS_MODE_BIG_ENDIAN

    return (dumper, arch, mode)




# xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx

class Dump:
    def __init__(self, arch, mode):
        self.arch = arch
        self.mode = mode
        self.method = self.Regs_method()
        self.register_names = self.Regs_register_names()
        self.registers = self.Regs_registers()
        self.mem_mmap = {}

    def Regs_method(self):
        assert (0)

    def Regs_register_names(self):
        assert (0)

    def Regs_registers(self):
        return self.arch.registers

    def getRegs(self):
        values = {}
        for regAddress in self.register_names:
            regName = self.register_names[regAddress]

            if regName in self.method:
                values[regAddress] = self.method[regName](regName)
                # print("success %-10s %x"%(regName,values[regAddress]))
            else:
                try:
                    values[regAddress] = idc.get_reg_value(regName)
                    # print("success %-10s %x"%(regName,values[regAddress]))
                except Exception as e:
                    print("filed  read regName %-10s %s" % (regName, e))
                    pass
        return values

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

    def writeMem(self, binfile):
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
        
        for regAddress in regs:
            INT = regs[regAddress]
            regName = self.register_names[regAddress]
            size = self.registers[regName][1]
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
                print(
                    " (%-10s IR_offset: %-5d) (regValue: %-32x nb: %2d) " % (regName, regAddress, (INT), len(db_data)))
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


class AMD64_dump(Dump):
    def __init__(self, arch, mode):
        Dump.__init__(self, arch, mode)

    # For instance, Microsoft Windows on x86-64 uses the GS segment to point to the Thread Environment Block, 
    # a small data structure for each thread, which contains information about exception handling, thread-local variables, 
    # and other per-thread state. Similarly, the Linux kernel uses the GS segment to store per-CPU data.
    # https://en.wikipedia.org/wiki/X86_memory_segmentation
    # Since Windbg debug module does not support get_thread_sreg_base()
    # we will call the debugger engine "dg" command and parse its output

    # linux gs -> not use 
    # linux fs -> fsbase = fs:[0x10] 
    #             thread_local | base | security(canry)
    #             mov dword ptr fs:[0xfffffffffffffffc], r8d 

    # windows gs -> TEB  gsbase = gs:[0x30]
    #             thread_local index in TEB:[0x58]
    # windows fs -> not use
    @staticmethod 
    def WindbgGetRegBase(tid):
        s = idc.Eval('WinDbgCommand("dg %x")' % cpu.fs)
        if "IDC_FAILURE" in s:
            return 0
        m = re.compile("[0-9a-f]{4} ([0-9a-f]{8})")
        t = m.match(s.split('\n')[-2])
        if not t:
            return 0
        return int(t.group(1), 16)
    @staticmethod 
    def get_gs_base_x86_64_windows(name):
        if "PE" not in idaapi.get_file_type_name():
            return 0
        # assert name == "gs"
        # windows
        sdb = 0
        for n in range(idaapi.get_segm_qty()):
            seg = idaapi.getnseg(n)
            sgname = idaapi.get_segm_name(seg, 0)
            if sgname.startswith('TIB['):
                _sdb = seg.start_ea + 0x1000
                sdb_self = int(base64.b16encode(idaapi.dbg_read_memory(_sdb + 0x30, 8)[::-1]), 16)
                if (sdb_self == _sdb):
                    sdb = _sdb
                    print("\nwarning: the segname:%s is zero,I give %016x" % (name, sdb))
                break
        if not sdb:
            idaapi.warning("\n\nwarning: the segname:%s is zero, U need set it by yourself\n" % (name))
        return sdb
    @staticmethod 
    def get_fs_base_x86_64_linux(name):
        if "ELF" not in idaapi.get_file_type_name():
            return 0
        # assert name == "gs"
        # WRFSBASE和WRGSBASE仅在64位模式下受支持。
        def patch_code(address, bytes_array):
            for code_byte in bytes_array:
                ida_bytes.patch_byte(address, code_byte)
                address = address + 1
                
        def part_code_run(params, store_regs, load_regs, insns, start_ea = idc.get_reg_value('rip')):
            store_code = b"".join(insns)
            length = len(store_code)
            end_ea = start_ea + len(store_code)
            
            backup_opcode = idc.get_bytes(start_ea, length)
            BackupRegs = { n : idc.get_reg_value('rip') for n in store_regs}
            for n, v in params.items():
                idc.set_reg_value(v, n)
            
            patch_code(start_ea, store_code)
            
            for count in insns:
                ida_dbg.step_into()
            print("step 1 %x"%start_ea)
            ida_dbg.wait_for_next_event(idaapi.STEP, -1)
            
            result = [ idc.get_reg_value(n) for n in load_regs]
            for n, v in BackupRegs.items():
                idc.set_reg_value(v, n)
            
            patch_code(start_ea, backup_opcode)
            return result
            
        
        # msr = GSMSR if name == "gs" else FSMSR
        # insns = [b'\x0f\x32'] # x86: rdmsr
        # eax, edx = part_code_run({"rcx":  msr & 0xFFFFFFFF }, ["rax", "rcx", "rdx", "rip"], ["eax", "edx"],  insns)
        # sdb = (edx << 32) | (eax & 0xFFFFFFFF)
        
        #code_hex = '65488B0425' # gs
        code_hex = '64488B0425' # fs
        
        code = [bytes.fromhex(code_hex) + struct.pack("<I", 0x10) # mov rax, qword ptr fs:[0x10]
               ]
        rax, = part_code_run({}, ["rax", "rip"], ["rax"],  code)
        
        selfptr = idc.get_qword(rax + 0x10)
        if rax and selfptr == rax:
            return rax
        idaapi.warning("\n\nwarning: the segname:%s is zero, U need set it by yourself\n" % (name))
        return 0
        

    def Regs_method(self):
        getF64 = lambda x: get_fpu_regs("ST%d" % (7 - int(x[2:])))[1]
        method = {
            'mm0': getF64,
            'mm1': getF64,
            'mm2': getF64,
            'mm3': getF64,
            'mm4': getF64,
            'mm5': getF64,
            'mm6': getF64,
            'mm7': getF64,
            'ymm0': get_ymm,
            'ymm1': get_ymm,
            'ymm2': get_ymm,
            'ymm3': get_ymm,
            'ymm4': get_ymm,
            'ymm5': get_ymm,
            'ymm6': get_ymm,
            'ymm7': get_ymm,
            'ymm8': get_ymm,
            'ymm9': get_ymm,
            'ymm10': get_ymm,
            'ymm11': get_ymm,
            'ymm12': get_ymm,
            'ymm13': get_ymm,
            'ymm14': get_ymm,
            'ymm15': get_ymm,
            'd': lambda name: 0xffffffffffffffff if idc.get_reg_value("DF") else 0x1,
            'fs': lambda name: AMD64_dump.get_gs_base_x86_64_windows(name),
            'gs': lambda name: AMD64_dump.get_fs_base_x86_64_linux(name),
            'fpround': getfpround,
            'sseround': getSseRound,
            'ftop': getftop,
            'fptag': getfpu_tags
        }
        return method

    def Regs_register_names(self):
        register_names = self.arch.register_names
        #print(register_names)
        register_names.pop(776) # fpreg
        for i in range(8):
            register_names[776 + i * 8] = "mm%d" % i
        return register_names

    def Regs_registers(self):
        return self.arch.registers


def align(a):
    return a & ~(0x1000 - 1)


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


class X86_dump(Dump):
    def __init__(self, arch, mode):
        Dump.__init__(self, arch, mode)

    def Regs_method(self):
        X86_EFLAGS_CF = 1 << 0
        X86_EFLAGS_FIXED = 1 << 1
        X86_EFLAGS_PF = 1 << 2
        X86_EFLAGS_AF = 1 << 4
        X86_EFLAGS_ZF = 1 << 6
        X86_EFLAGS_SF = 1 << 7
        X86_EFLAGS_TF = 1 << 8
        X86_EFLAGS_IF = 1 << 9
        X86_EFLAGS_DF = 1 << 10
        X86_EFLAGS_OF = 1 << 11
        X86_EFLAGS_IOPL = 1 << 12
        X86_EFLAGS_IOPL_MASK = 3 << 12
        X86_EFLAGS_NT = 1 << 14
        X86_EFLAGS_RF = 1 << 16
        X86_EFLAGS_VM = 1 << 17
        X86_EFLAGS_AC = 1 << 18
        X86_EFLAGS_VIF = 1 << 19
        X86_EFLAGS_VIP = 1 << 20
        X86_EFLAGS_ID = 1 << 21

        getF64 = lambda x: get_fpu_regs("ST%d" % (7 - int(x[2:])))[1]

        method = {
            'mm0': getF64,
            'mm1': getF64,
            'mm2': getF64,
            'mm3': getF64,
            'mm4': getF64,
            'mm5': getF64,
            'mm6': getF64,
            'mm7': getF64,
            'xmm0': get_ymm,
            'xmm1': get_ymm,
            'xmm2': get_ymm,
            'xmm3': get_ymm,
            'xmm4': get_ymm,
            'xmm5': get_ymm,
            'xmm6': get_ymm,
            'xmm7': get_ymm,
            'xmm8': get_ymm,
            'xmm9': get_ymm,
            'xmm10': get_ymm,
            'xmm11': get_ymm,
            'xmm12': get_ymm,
            'xmm13': get_ymm,
            'xmm14': get_ymm,
            'xmm15': get_ymm,
            'd': lambda name: 0xffffffff if idc.get_reg_value("DF") else 0x1,
            'gdt': lambda name: GDT_MAP_ADDR,
            'fpround': getfpround,
            'sseround': getSseRound,
            'ftop': getftop,
            'fptag': getfpu_tags
        }
        return method

    def Regs_register_names(self):
        register_names = self.arch.register_names
        register_names.pop(72)# fpreg
        for i in range(8):
            register_names[72 + i * 8] = "mm%d" % i
        return register_names

    def init_segm_mem(self):
        # Windows only
        # fs halways not zero
        segment = {}
        gdt = gdt32(GDT_MAP_ADDR)
        
        lreg_base = lambda name : idaapi.dbg_get_thread_sreg_base(idc.get_current_thread(), int(getattr(cpu, name)))
        sregs = ["cs", "ds", "es", "ss", "fs", "gs"]
        
        limit = 0x1000
        DPL = 1
        S = 0
        TYPE = 0
        
        G = 1
        D = 0
        L = 1
        AVL = 0
        flags = (G << 3) | (D << 2) | (L << 1) | AVL
        
        for sreg in sregs:
            idx = idc.get_reg_value(sreg)
            base = lreg_base(sreg)
            print("sreg :{} idx :{}  {}.base :0x{:x}".format(sreg, idx, sreg, base))
            gdt.addSegDiscription(idx, base, limit, DPL, S, TYPE, flags=flags)
        
        
        return gdt.get_gdt()


dump_class_obj = None
def doit(dump_class_obj):
    bin_path = ida_loader.get_path(ida_loader.PATH_TYPE_CMD)
    bin_path = bin_path
    binfile = open(bin_path + '.dump', 'wb+')
    dump_class_obj.writeMem(binfile)
    binfile.close()
    print('dump success: ', bin_path + '.dump')


class myplugin_t(idaapi.plugin_t):
    flags = idaapi.PLUGIN_UNL
    comment = "This is a comment bin"

    help = "This is help bin"
    wanted_name = "TriggerBug memdump"
    wanted_hotkey = "Shift-2"

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
        doit(dump_class_obj)

    def term(self):
        idaapi.msg("term() called!\n")


def PLUGIN_ENTRY():
    return myplugin_t()



