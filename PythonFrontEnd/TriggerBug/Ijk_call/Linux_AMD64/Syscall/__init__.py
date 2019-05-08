import logging
import traceback
from ..z3 import z3
from ..TriggerBugConst import *
from ..TriggerBug import *
# from .file_system import File_System
# from .std_system import Std_System
# from .Description import Des_Manager
l = logging.getLogger(name=__name__)



def align(a, size):
    return a & ~(size - 1)


def setRax(state, value):
    state.reg_w('rax', value)
    l.info("i return %x > eax", value)


tmp_brk = align(0x0000000000603000, 32)


def getRegs(state):
    return state.eax, state.rbx, state.rdi, state.rsi, state.rdx


def getStr(state, address):
    tmp = ''
    bv = state.mem_r(address, 1)
    while bv.args[0] != 0:
        if bv.symbolic:
            raise Exception("cant get symbolic str:%s at 0x%x" % (tmp, address))
        tmp += chr(bv.args[0])
        address += 1
        bv = state.mem_r(address, 1)
    return tmp

flagcount=0
def sys_0(state):  # read  fd l_rdi ,  buff  l_rsi ,l_rdx n
    eax, rbx, rdi, rsi, rdx = getRegs(state)
    l.info('system call: read fd:0x%x buff:0x%x count:0x%x', rdi, rsi, rdx)
    n=rdx
    if(rdi==0):
        for i in range(n):
            global flagcount
            k=z3.BitVec('flag_%d' % flagcount, 8, state.ctx)
            flagcount=flagcount+1
            state.add(k >= 7,True)
            state.add(k < 127,True)
            state.mem_write(rsi+i,k,1)

        state.mem_write(rsi+1,0,1)
        state.regs_write("rax", n)
        return Running


    #
    # setRax(state, state.des_manager[rdi].read(state))
    #     print('need input %d' % rdx)
    #     string = [_ for _ in input().encode()][:rdx]
    #     if string == []:
    #         state.mem_w(rsi, ord('\n'), 1)
    #     else:
    #         state.mem_w(rsi, string)
    #     print('input %s' % string)
    #     setRax(state, rdx)
    # elif state.file_system.is_exist(rdi):
    #     value = state.file_system.read(rdi, rdx)
    #     if isinstance(value, str):
    #         value = value.encode()
    #     state.mem_w(rsi, [_ for _ in value])
    #     setRax(state, len(value))
    # else:
    #     setRax(state, -1)
    #     l.info('\033[1;33;44m un know 套接字0x%x \033[0m', rdi)


def sys_1(state):  # write  fd l_rdi ,  buff  l_rsi ,l_rdx n
    eax, rbx, rdi, rsi, rdx = getRegs(state)
    l.info('system call: write fd:0x%x buff:0x%x count:0x%x', rdi, rsi, rdx)
    if rdi == 1:
        s = ''
        for count in range(rdx):
            char = state.mem_r(rsi + count, 1)
            s += chr(char)
        l.info('\033[1;33;44m stdout:%s\033[0m', s)
        setRax(state, rdx)
    elif rdi == 2:
        s = ''
        for count in range(rdx):
            char = state.mem_r(rsi + count, 1)
            s += chr(char)
        l.info('\033[1;33;44m stderr:%s\033[0m', s)
        setRax(state, rdx)
        return Death
    elif state.file_system.is_exist(rdi):
        value = state.mem_r(rsi, rdx)
        setRax(state, state.file_system.write(rdi, value.chop(8)))
    else:
        s = ''
        for count in range(rdx):
            char = state.mem_r(rsi + count, 1)
            state.mem_w(rdi + count, char, 1)
            s += chr(char)
        l.info('\033[1;33;44m write:%s\033[0m', s)
        setRax(state, rdx)

    return Running

def sys_3(state):  # close
    eax, rbx, rdi, rsi, rdx = getRegs(state)
    l.info('system call: close description:0x%x', rdi)
    ShowRegs(state)
    setRax(state, state.file_system.close(state))


def sys_12(state):  # 0xc brk
    global tmp_brk
    eax, rbx, rdi, rsi, rdx = getRegs(state)
    l.info('system call: brk address:0x%x', rbx)
    ShowRegs(state)
    brk = rbx
    if brk == 0:
        pass
    else:
        if brk < tmp_brk:
            state.mem_unmap(brk, tmp_brk)
            tmp_brk = align(brk, 32)
        elif brk == tmp_brk:
            state.mem_map(tmp_brk, tmp_brk + 0x21000, claripy.BVV(0, 8))
            tmp_brk = align(tmp_brk + 0x21000, 32)
        else:
            state.mem_map(tmp_brk, brk, claripy.BVV(0, 8))
            tmp_brk = align(brk, 32)
    setRax(state, tmp_brk)


def sys_257(state):  # rsi filename   rdx flag
    eax, rbx, rdi, rsi, rdx = getRegs(state)
    filename = getStr(state, rsi)
    l.info('system call:sync_file_range name:0x%x flag:0x%x', rsi, rdx)
    # ShowRegs(state)
    result = state.file_system.sync_file_range(filename=filename, flags=rdx)
    setRax(state, result)

def sys_5(state):
    eax, rbx, rdi, rsi, rdx = getRegs(state)
    l.info('system call: sys_newfstat fd:0x%x 	struct stat __user *statbuf:0x%x', rdi, rsi)
    state.regs_write("rax",0)
    return Running
def sys_35(state):#sys_nanosleep

    state.regs_write("rax", 0)
    return Running
    pass

def deal_sys_call(state):
    eax = state.eax
    address=state.guest_start
    try:
        l.info("Ijk_Sys_call #address:%x eax:0x%x", address, eax)
        return globals()['sys_' + str(eax)](state)
    except Exception as e:
        traceback.print_exc()
        l.error("error:%s Ijk_Sys_call #address:%s eax:0x%x", e, address, eax)
        state.regs_write("rax", 0)
        return Running
