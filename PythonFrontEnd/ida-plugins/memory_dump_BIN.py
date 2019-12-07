# encoding:utf-8
from __future__ import print_function
import idaapi
import idc
import idautils
import sys
import struct
import time
import pyvex
import archinfo  # 没有pyvex则archinfo无法工作
import ctypes
import re
import base64

arch = None
mode = None
GDT_MAP_ADDR = 0xfff00000


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


BPNORMAL = 0
BPHARDWARE = 1
UE_HARDWARE_EXECUTE = 4
UE_HARDWARE_WRITE = 5
UE_HARDWARE_READWRITE = 6
UE_HARDWARE_SIZE_1 = 7
UE_HARDWARE_SIZE_2 = 8
UE_HARDWARE_SIZE_4 = 9
UE_HARDWARE_SIZE_8 = 10


def Breakpoints():
    count = GetBptQty()
    for i in range(0, count):
        ea = GetBptEA(i)
        bpt = idaapi.bpt_t()
        if not idaapi.get_bpt(ea, bpt):
            continue
        if bpt.type & BPT_SOFT != 0:
            yield (ea, BPNORMAL, 0, Word(ea))
        else:
            bptype = BPNORMAL if bpt.type == BPT_DEFAULT else BPHARDWARE
            hwtype = {
                BPT_WRITE: UE_HARDWARE_WRITE,
                BPT_RDWR: UE_HARDWARE_READWRITE,
                BPT_EXEC: UE_HARDWARE_EXECUTE
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


def get_hardware_mode():
    (arch, mode) = (None, None)
    info = idaapi.get_inf_structure()
    # heuristically detect hardware setup
    info = idaapi.get_inf_structure()

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

    if cpuname == "metapc":
        if info.is_64bit():
            arch = archinfo.ArchAMD64()
            mode = KS_MODE_64
        elif info.is_32bit():
            arch = archinfo.ArchX86()
            mode = KS_MODE_32
        else:
            arch = archinfo.ArchNotFound()
            mode = KS_MODE_16

    elif cpuname.startswith("ppc"):
        if info.is_64bit():
            arch = archinfo.ArchPPC64()
            mode = KS_MODE_PPC64
        else:
            arch = archinfo.ArchPPC32()
            mode = KS_MODE_PPC32
        if cpuname == "ppc":
            # do not support Little Endian mode for PPC
            mode += KS_MODE_BIG_ENDIAN

    elif cpuname.startswith("mips"):
        if info.is_64bit():
            arch = archinfo.ArchMIPS64()
            mode = KS_MODE_MIPS64
        else:
            arch = archinfo.ArchMIPS32()
            mode = KS_MODE_MIPS32
    elif cpuname.startswith("systemz") or cpuname.startswith("s390x"):
        arch = archinfo.ArchS390X()
        mode = KS_MODE_BIG_ENDIAN

    return (arch, mode)


# xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx

def getfpround(name):
    assert (name == 'fpround')
    return (idc.GetRegValue('CTRL') >> 10) & 0b11


def getSseRound(name):
    assert (name == 'sseround')
    return (idc.GetRegValue('MXCSR') >> 13) & 0b11


def getftop(name):
    assert (name == 'ftop')
    return ((idc.GetRegValue('STAT') >> 11) & 0b111) - 8


def getfpu_tags(name):
    assert (name == 'fptag')
    re = 0
    tag = idc.GetRegValue('TAGS')
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


def get_xmm(name):
    rv = idaapi.regval_t()
    if idaapi.get_reg_val(name, rv):
        return int(rv.bytes()[::-1].encode('hex'), 16)
    raise ('fk names')


def get_ymm(name):
    print("warning: ida not support reg: %s , set high 16 bytes zero" % (name))
    return get_xmm("x" + name[1:])


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
                    values[regAddress] = idc.GetRegValue(regName)
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
            b += struct.pack("<B", idc.Byte(ea + (size & (~7)) + i))

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
        idaapi.refresh_debugger_memory()
        print("+-------------------+----------------------+--------------------+----------+--------+")
        print("|      segment      |          VA          |        size        |   flag   | status |")
        print("+-------------------+----------------------+--------------------+----------+--------+")

        for n in xrange(idaapi.get_segm_qty()):
            seg = idaapi.getnseg(n)
            if seg:
                name = Dump.getSegName(seg, segm)
                address = seg.startEA
                length = seg.endEA - seg.startEA

                db_data = idaapi.dbg_read_memory(address, length)
                print("| %-17s |  %18x  | %8x -> %5dkb|    %2d    |   " % (
                name, address, length, length / 1024, seg.flags), end="")
                if db_data:
                    segm[name] = [address, length, db_data]
                    print('ok   |')
                    length = len(db_data)
                    segm[name] = [address, length, db_data]
                else:
                    if (length >= 0x400):
                        print(
                            "war  |\n+-------------------+----------------------+--------------------+----------+--------+")
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
                                    print("| %-17s |  %18x  | %8x -> %5dkb|    %2d    |  faild |" % (
                                    name, fbegin, fsize, fsize / 1024, seg.flags))
                                else:  # 0 0
                                    fsize += size
                                    if (i == len(data) - 1):
                                        print("| %-17s |  %18x  | %8x -> %5dkb|    %2d    |  faild |" % (
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
                                        print("| %-17s |  %18x  | %8x -> %5dkb|    %2d    |   ok   |" % (
                                        name, begin, len(tmp), len(tmp) / 1024, seg.flags))
                                    else:
                                        print("| %-17s |  %18x  | %8x -> %5dkb|    %2d    |  faild |" % (
                                        name, fbegin, fsize, fsize / 1024, seg.flags))
                                        break

                        print("+-------------------+----------------------+--------------------+----------+--------+")
                    else:
                        print('  faild')
                    continue

        print("+-------------------+----------------------+--------------------+----------+--------+")
        # GetBptQty() GetBptEA(n):
        nameoffset_p = 0
        dataoffset_p = 0
        all_ab_name = 0

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
                db_data = db_data[:offset] + struct.pack(up("<H"), code) + db_data[offset + 2:]
                segm[name] = [address, length, db_data]
                assert (len(db_data) == len_db_data)
                print ("bkp found: address: %x code: %s"%(address+offset, base64.b16encode(struct.pack(up("<H"), code))))


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


def get_sreg_base_x64(name):
    sdb = idaapi.dbg_get_thread_sreg_base(idc.GetCurrentThreadId(), int(getattr(cpu, name)))
    if not sdb:
        for n in xrange(idaapi.get_segm_qty()):
            seg = idaapi.getnseg(n)
            sgname = idaapi.get_segm_name(seg, 0)
            if sgname.startswith('TIB['):
                _sdb = seg.startEA + 0x1000
                sdb_self = int(base64.b16encode(idaapi.dbg_read_memory(_sdb + 0x30, 8)[::-1]), 16)
                if (sdb_self == _sdb):
                    sdb = _sdb
                    print("\nwarning: the segname:%s is zero,I give %016x" % (name, sdb))
                break
    if not sdb:
        print("\n\nwarning: the segname:%s is zero, U need set it by yourself\n" % (name))
    return sdb


class AMD64_dump(Dump):
    def __init__(self, arch, mode):
        Dump.__init__(self, arch, mode)

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
            'd': lambda name: 0xffffffffffffffff if idc.GetRegValue("DF") else 0x1,
            'fs': lambda name: get_sreg_base_x64(name),
            'gs': lambda name: get_sreg_base_x64(name),
            'fpround': getfpround,
            'sseround': getSseRound,
            'ftop': getftop,
            'fptag': getfpu_tags
        }
        return method

    def Regs_register_names(self):
        register_names = self.arch.register_names
        register_names.pop(776)
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
        to_ret |= (
                              flags & 0xf) << 52;  # [52:56]    flag: G<<3|D<<2|0<1|AVL (各1bit )如果G=0那么段大小为0~1MB, G=1段大小为4KB~4GB  D或B 这个我还没搞懂 以后再说只要知道32位访问为1 AVL: linux忽略这个
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
            'xmm0': get_xmm,
            'xmm1': get_xmm,
            'xmm2': get_xmm,
            'xmm3': get_xmm,
            'xmm4': get_xmm,
            'xmm5': get_xmm,
            'xmm6': get_xmm,
            'xmm7': get_xmm,
            'xmm8': get_xmm,
            'xmm9': get_xmm,
            'xmm10': get_xmm,
            'xmm11': get_xmm,
            'xmm12': get_xmm,
            'xmm13': get_xmm,
            'xmm14': get_xmm,
            'xmm15': get_xmm,
            'd': lambda name: 0xffffffff if idc.GetRegValue("DF") else 0x1,
            'gdt': lambda name: GDT_MAP_ADDR,
            'fpround': getfpround,
            'sseround': getSseRound,
            'ftop': getftop,
            'fptag': getfpu_tags
        }
        return method

    def Regs_register_names(self):
        register_names = self.arch.register_names
        register_names.pop(72)
        for i in range(8):
            register_names[72 + i * 8] = "mm%d" % i
        return register_names

    def init_segm_mem(self):
        segment = {}
        gdt = gdt32(GDT_MAP_ADDR)
        fs_idx = idc.GetRegValue('fs')
        gs_idx = idc.GetRegValue('gs')
        fs_addr = idaapi.dbg_get_thread_sreg_base(idc.GetCurrentThreadId(), int(cpu.fs))
        gs_addr = idaapi.dbg_get_thread_sreg_base(idc.GetCurrentThreadId(), int(cpu.gs))
        G = 1
        D = 0
        L = 1
        AVL = 0
        gdt.addSegDiscription(fs_idx, fs_addr, 0x1000, 1, 0, 0, (G << 3) | (D << 2) | (L << 1) | AVL)
        gdt.addSegDiscription(gs_idx, gs_addr, 0x1000, 1, 0, 0, (G << 3) | (D << 2) | (L << 1) | AVL)
        return gdt.get_gdt()


dump_class_obj = None
def doit():
    global dump_class_obj
    if isinstance(arch, archinfo.ArchX86):
        dump_class_obj = X86_dump(arch, mode)
    elif isinstance(arch, archinfo.ArchAMD64):
        dump_class_obj = AMD64_dump(arch, mode)

    bin_path = ida_loader.get_path(ida_loader.PATH_TYPE_CMD)
    bin_path = bin_path.decode("utf8")
    binfile = open(bin_path + b'.dump', 'wb+')
    dump_class_obj.writeMem(binfile)
    binfile.close()
    print('dump success: ', bin_path + '.dump')


class myplugin_t(idaapi.plugin_t):
    flags = idaapi.PLUGIN_UNL
    comment = "This is a comment bin"

    help = "This is help bin"
    wanted_name = "My Python plugin bin"
    wanted_hotkey = "Shift-2"

    def init(self):
        return idaapi.PLUGIN_OK

    def run(self, arg):
        global arch, mode
        arch, mode = get_hardware_mode()
        doit()

    def term(self):
        idaapi.msg("term() called!\n")


def PLUGIN_ENTRY():
    return myplugin_t()
