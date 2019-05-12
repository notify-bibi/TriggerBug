# encoding:utf-8
from __future__ import print_function
import idaapi
import idc
import idautils
import sys
import struct
import time

class PickleSegmentData():
    def __init__(self, name, segmentdata, startEA, endEA):
        self.name = name
        self.segmentdata = segmentdata
        self.startEA = startEA
        self.endEA = endEA

def writeMem(binfile,regs):
    segm={}
    for n in xrange(idaapi.get_segm_qty()):
        seg = idaapi.getnseg(n)
        if seg:
            count=0
            h=''
            while (idaapi.get_segm_name(seg, 0)+h) in segm.keys():
                count+=1
                h = str(count)
            name=idaapi.get_segm_name(seg, 0)+h
            address=seg.startEA
            length=seg.endEA-seg.startEA
            
            db_data=idaapi.dbg_read_memory(address,length)
            if db_data:
                print('ok   ',name,seg.flags,length,'bytes',length/1024,'kb')
                segm[name]=[address,length,db_data]
            else:
                print('faild',name,seg.flags,length,'bytes',length/1024,'kb')
                pass
    nameoffset_p=0
    dataoffset_p=0
    all_ab_name=0
    
    register_names={16: 'rax', 24: 'rcx', 32: 'rdx', 40: 'rbx', 48: 'rsp', 56: 'rbp', 64: 'rsi', 72: 'rdi', 80: 'r8', 88: 'r9', 96: 'r10', 104: 'r11', 112: 'r12', 120: 'r13', 128: 'r14', 136: 'r15', 144: 'cc_op', 152: 'cc_dep1', 160: 'cc_dep2', 168: 'cc_ndep', 176: 'd', 184: 'rip', 192: 'ac', 200: 'id', 208: 'fs', 216: 'sseround', 224: 'ymm0', 256: 'ymm1', 288: 'ymm2', 320: 'ymm3', 352: 'ymm4', 384: 'ymm5', 416: 'ymm6', 448: 'ymm7', 480: 'ymm8', 512: 'ymm9', 544: 'ymm10', 576: 'ymm11', 608: 'ymm12', 640: 'ymm13', 672: 'ymm14', 704: 'ymm15', 736: 'ymm16', 768: 'ftop', 776: 'mm0',784: "mm1",792: "mm2",800: "mm3",808: "mm4",816: "mm5",824: "mm6",832: "mm7", 840: 'fptag', 848: 'fpround', 856: 'fc3210', 864: 'emnote', 872: 'cmstart', 880: 'cmlen', 888: 'nraddr', 904: 'gs', 912: 'ip_at_syscall'}
    registers= {'rax': (16, 8), 'eax': (16, 4), 'ax': (16, 2), 'al': (16, 1), 'ah': (17, 1), 'rcx': (24, 8), 'ecx': (24, 4), 'cx': (24, 2), 'cl': (24, 1), 'ch': (25, 1), 'rdx': (32, 8), 'edx': (32, 4), 'dx': (32, 2), 'dl': (32, 1), 'dh': (33, 1), 'rbx': (40, 8), 'ebx': (40, 4), 'bx': (40, 2), 'bl': (40, 1), 'bh': (41, 1), 'rsp': (48, 8), 'sp': (48, 8), 'esp': (48, 4), 'rbp': (56, 8), 'bp': (56, 8), 'ebp': (56, 4), 'rsi': (64, 8), 'esi': (64, 4), 'si': (64, 2), 'sil': (64, 1), 'sih': (65, 1), 'rdi': (72, 8), 'edi': (72, 4), 'di': (72, 2), 'dil': (72, 1), 'dih': (73, 1), 'r8': (80, 8), 'r9': (88, 8), 'r10': (96, 8), 'r11': (104, 8), 'r12': (112, 8), 'r13': (120, 8), 'r14': (128, 8), 'r15': (136, 8), 'cc_op': (144, 8), 'cc_dep1': (152, 8), 'cc_dep2': (160, 8), 'cc_ndep': (168, 8), 'd': (176, 8), 'dflag': (176, 8), 'rip': (184, 8), 'ip': (184, 8), 'pc': (184, 8), 'ac': (192, 8), 'acflag': (192, 8), 'id': (200, 8), 'idflag': (200, 8), 'fs': (208, 8), 'fs_const': (208, 8), 'sseround': (216, 8), 'ymm0': (224, 32), 'xmm0': (224, 16), 'ymm1': (256, 32), 'xmm1': (256, 16), 'ymm2': (288, 32), 'xmm2': (288, 16), 'ymm3': (320, 32), 'xmm3': (320, 16), 'ymm4': (352, 32), 'xmm4': (352, 16), 'ymm5': (384, 32), 'xmm5': (384, 16), 'ymm6': (416, 32), 'xmm6': (416, 16), 'ymm7': (448, 32), 'xmm7': (448, 16), 'ymm8': (480, 32), 'xmm8': (480, 16), 'ymm9': (512, 32), 'xmm9': (512, 16), 'ymm10': (544, 32), 'xmm10': (544, 16), 'ymm11': (576, 32), 'xmm11': (576, 16), 'ymm12': (608, 32), 'xmm12': (608, 16), 'ymm13': (640, 32), 'xmm13': (640, 16), 'ymm14': (672, 32), 'xmm14': (672, 16), 'ymm15': (704, 32), 'xmm15': (704, 16), 'ymm16': (736, 32), 'xmm16': (736, 16), 'ftop': (768, 4), 'fpreg': (776, 64), 'fpu_regs': (776, 64), 'mm0': (776, 8), 'mm1': (784, 8), 'mm2': (792, 8), 'mm3': (800, 8), 'mm4': (808, 8), 'mm5': (816, 8), 'mm6': (824, 8), 'mm7': (832, 8), 'fptag': (840, 8), 'fpu_tags': (840, 8), 'fpround': (848, 8), 'fc3210': (856, 8), 'emnote': (864, 4), 'cmstart': (872, 8), 'cmlen': (880, 8), 'nraddr': (888, 8), 'gs': (904, 8), 'gs_const': (904, 8), 'ip_at_syscall': (912, 8)}
    
    for regAddress in regs:
        INT=regs[regAddress]
        regName = register_names[regAddress]
        size=registers[regName][1]
        if size==1:
            db_data=struct.pack("<B",INT)
        elif size==2:
            db_data=struct.pack("<H",INT)
        elif size==4:
            db_data=struct.pack("<I",INT)
        elif size==8:
            db_data=struct.pack("<Q",INT)
        elif size==16:
            db_data=struct.pack("<QQ",int(INT&0xffffffffffffffff),int(INT>>64))
        elif size==32:
            db_data=struct.pack("<QQQQ",INT&0xffffffffffffffff,(INT>>64)&0xffffffffffffffff,(INT>>128)&0xffffffffffffffff,INT>>192)
        else:
            continue
        segm['registers'+str(regAddress)]=[regAddress,len(db_data),db_data]
        
    for name in segm:
        address,length,db_data=segm[name]
        ab_name=(name+'\x00').encode('utf-8')
        all_ab_name+=len(ab_name)
    for name in segm:
        address,length,db_data=segm[name]
        ab_name=(name+'\x00').encode('utf-8')
        nameoffset=len(segm)*32+nameoffset_p
        dataoffset=len(segm)*32+all_ab_name+dataoffset_p
        db1=struct.pack("<Q",nameoffset)
        db2=struct.pack("<Q",address)
        db3=struct.pack("<Q",length)
        db4=struct.pack("<Q",dataoffset)
        binfile.write(db1)
        binfile.write(db2)
        binfile.write(db3)
        binfile.write(db4)
        nameoffset_p+=len(ab_name)
        dataoffset_p+=length
    for name in segm:
        address,length,db_data=segm[name]
        ab_name=(name+'\x00').encode('utf-8')
        binfile.write(ab_name)
    for name in segm:
        address,length,db_data=segm[name]
        binfile.write(db_data)
def getfpround(name):
    assert(name=='fpround')
    return (idc.GetRegValue('CTRL')>>10)&0b11
    
def getSseRound(name):
    assert(name=='sseround')
    return (idc.GetRegValue('MXCSR')>>13)&0b11
    
def getftop(name):
    assert(name=='ftop')
    return (idc.GetRegValue('STAT')>>11)&0b111
    
def getfpu_tags(name):
    assert(name=='fpu_tags')
    return (idc.GetRegValue('TAGS')>>11)&0b111
    
    
def get_xmm(s):
    rv = idaapi.regval_t()
    if idaapi.get_reg_val(s, rv):
        return int(rv.bytes()[::-1].encode('hex'),16)
    raise('fk names')
    
def getRegs():
    
    register_names={16: 'rax', 24: 'rcx', 32: 'rdx', 40: 'rbx', 48: 'rsp', 56: 'rbp', 64: 'rsi', 72: 'rdi', 80: 'r8', 88: 'r9', 96: 'r10', 104: 'r11', 112: 'r12', 120: 'r13', 128: 'r14', 136: 'r15', 144: 'cc_op', 152: 'cc_dep1', 160: 'cc_dep2', 168: 'cc_ndep', 176: 'd', 184: 'rip', 192: 'ac', 200: 'id', 208: 'fs', 216: 'sseround', 224: 'ymm0', 256: 'ymm1', 288: 'ymm2', 320: 'ymm3', 352: 'ymm4', 384: 'ymm5', 416: 'ymm6', 448: 'ymm7', 480: 'ymm8', 512: 'ymm9', 544: 'ymm10', 576: 'ymm11', 608: 'ymm12', 640: 'ymm13', 672: 'ymm14', 704: 'ymm15', 736: 'ymm16', 768: 'ftop', 776: 'mm0',784: "mm1",792: "mm2",800: "mm3",808: "mm4",816: "mm5",824: "mm6",832: "mm7", 840: 'fptag', 848: 'fpround', 856: 'fc3210', 864: 'emnote', 872: 'cmstart', 880: 'cmlen', 888: 'nraddr', 904: 'gs', 912: 'ip_at_syscall'}
    values={}
    method={
    'mm0':get_xmm,
    'mm1':get_xmm,
    'mm2':get_xmm,
    'mm3':get_xmm,
    'mm4':get_xmm,
    'mm5':get_xmm,
    'mm6':get_xmm,
    'mm7':get_xmm,
    'xmm0':get_xmm,
    'xmm1':get_xmm,
    'xmm2':get_xmm,
    'xmm3':get_xmm,
    'xmm4':get_xmm,
    'xmm5':get_xmm,
    'xmm6':get_xmm,
    'xmm7':get_xmm,
    'xmm8':get_xmm,
    'xmm9':get_xmm,
    'xmm10':get_xmm,
    'xmm11':get_xmm,
    'xmm12':get_xmm,
    'xmm13':get_xmm,
    'xmm14':get_xmm,
    'xmm15':get_xmm,
    'fs': lambda name : idaapi.dbg_get_thread_sreg_base(idc.GetCurrentThreadId(),int(cpu.fs)),
    'gs': lambda name : idaapi.dbg_get_thread_sreg_base(idc.GetCurrentThreadId(),int(cpu.gs)),
    'fpround':getfpround,
    'sseround':getSseRound,
    'ftop':getftop
    # 'fpu_tags':getfpu_tags
    }
    
    for regAddress in register_names:
        regName = register_names[regAddress]
        
        if regName in method:
            values[regAddress]=method[regName](regName)
            print("success %-10s %x"%(regName,values[regAddress]))
        else:
            try:
                values[regAddress]=idc.GetRegValue(regName )
                print("success %-10s %x"%(regName,values[regAddress]))
            except Exception as e:
                print("filed  read regName %-10s %s"%(regName,e))
                pass
    return values
def doit():
    Regs=getRegs()
    
    bin_path=ida_loader.get_path(ida_loader.PATH_TYPE_CMD)
    bin_path=bin_path.decode("utf8")
    binfile = open(bin_path+b'.dump', 'wb+')
    writeMem(binfile,Regs)
    binfile.close()
    print('dump success: ',bin_path+'.dump')
        

class myplugin_t(idaapi.plugin_t):
    flags = idaapi.PLUGIN_UNL
    comment = "This is a comment bin"

    help = "This is help bin"
    wanted_name = "My Python plugin bin"
    wanted_hotkey = "Shift-2"

    def init(self):
        idaapi.msg("init() called!\n")
        return idaapi.PLUGIN_OK

    def run(self, arg):
        doit()
        
    def term(self):
        idaapi.msg("term() called!\n")

def PLUGIN_ENTRY():
    return myplugin_t()
