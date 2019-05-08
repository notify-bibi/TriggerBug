#!/usr/bin/env python
# coding=utf-8
import angr,string
import claripy
import pickle
import sys
import logging
import time
logging.getLogger('angr').setLevel('WARNING')
def pickle_read(file_name):
    pickle_file = open(file_name, 'rb')
    my_list = pickle.load(pickle_file)
    pickle_file.close()
    return my_list
def pickle_write(file_name, data):
	pickle_file = open(file_name, 'wb')
	pickle.dump(data, pickle_file)
	pickle_file.close()

p = angr.Project('./asong', load_options={'auto_load_libs': False})

def decode1(dedata):
    filename = 'that_girl'
    thatgirl=''
    filethat = open(filename, 'r')
    thatgirl = filethat.read()
    filethat.close()
    filesize = len(thatgirl)
    @p.hook(0x00000000000400F67, length=0)
    def readfile1(_state):
        global t
        t = time.time()
        print(_state, 'start readfile;')
    @p.hook(0x00000000000400F6C, length=0)
    def readfile2(_state):
        global t
        print(_state, 'end readfile;')
        print(time.time() - t)


    @p.hook(0x00000400E8C, length=0)
    def count(_state):
        print(_state.regs.eax)

    # In[6]: claripy.BVV(0x12, 16).reversed
    # Out[6]: < BV16 0x1200 >

    # In[7]: claripy.BVV(0x12, 16)
    # Out[7]: < BV16 0x12 >
    need=[]
    @p.hook(0x00000000000400EC5, length=0)
    def solvaddrs(_state):
        index = _state.solver.eval(_state.regs.rax)*8
        _state.solver.add(dedata.reversed[index+7:index] == _state.regs.dl)
        if index in need:
            _state.solver.add(False)
            _state.downsize()
        if _state.satisfiable():
            print(True)
            print(_state.solver.eval(flag,cast_to=bytes))
            need.append(index)
        else:
            _state.solver.add(False)
            _state.downsize()
    thatgirl_symbols = [claripy.BVV(ord(thatgirl[i]), 8) for i in range(filesize)]
    thatgirlContent = claripy.Concat(*thatgirl_symbols)
    simfile = angr.SimFile('./that_girl', content=thatgirlContent,size=filesize, has_end=angr.options.FILES_HAVE_EOF)

    flag_chars = [claripy.BVS('flag_%d' % i, 8) for i in range(38+5)]
    flag = claripy.Concat(*flag_chars +[claripy.BVV(b'}')]+ [claripy.BVV(b'\n')])

    state = p.factory.entry_state(
        add_options=angr.options.unicorn | {angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY,  angr.options.REPLACEMENT_SOLVER},
        stdin=flag,
        remove_options={angr.options.LAZY_SOLVES}
    )
    #state.options.add(angr.options.LAZY_SOLVES)
    state.fs.insert('that_girl', simfile)
    for k in flag_chars:
        state.solver.add(k != 10)
        so1=state.solver.And( k > 8, k < 14)
        so2=state.solver.And( k > 31, k < 127)
        state.solver.add(state.solver.Or(so1,so2)==True)
    simulation = p.factory.simulation_manager(state)
    res = simulation.explore(find=0x00000000400EEC, avoid=[0x000400C36], enable_veritesting=True)
    #Threading
    print(len(res.found))
    for pp in res.found:
        print(pp.posix.dumps(0))  
        #addr = pp.memory.load(pp.regs.rbp-0x10, 8, endness='Iend_LE')


def decode2():  # 400DB4
    unknow = 'EC 29 E3 41 E1 F7 AA 1D 29 ED 29 99 39 F3 B7 A9 E7 AC 2B B7 AB 40 9F A9 31 35 2C 29 EF A8 3D 4B B0 E9 E1 68 7B 41'
    unknow2 = unknow.replace(' ', '')
    unknow3 = claripy.BVV(int(unknow2, 16), 38*8)
    symbols = [claripy.BVS('crypto%d' % i, 8) for i in range(38)]
    Content = claripy.Concat(*symbols)
    state = p.factory.blank_state(
        addr=0x0000000400EDB,
        #add_options=angr.options.unicorn, #| {angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY},
        remove_options={}
    )

    @p.hook(0x00000000400EE7, length=0)
    def index(_state):
        print(_state, 'index', _state.regs.esi)
    state.regs.rbp = state.regs.rsp+0x60
    print('ss', state.regs.rbp-0x40)
    state.memory.store(state.regs.rbp-0x40, Content,38)
    state.memory.store(state.regs.rbp-0x44, 38, 4, endness='Iend_LE')
    simulation = p.factory.simulation_manager(state)
    res = simulation.explore(find=0x00000400EEC)  # , enable_veritesting=True
    print(len(res.found))
    result=[]
    for pp in res.found:
        print('ss',pp.regs.rbp-0x40)
        BV_strCpySrc = pp.memory.load(pp.regs.rbp-0x40, 38)
        pp.solver.add(BV_strCpySrc == unknow3)
        if pp.satisfiable():
            tmp = pp.solver.eval(Content, cast_to=bytes)
            print('yes')
            result.append(tmp)
        else:
            print('no')
    return result[0]


def decode3(dedata):  # 400D33
    symbols = [claripy.BVS('crypto%d' % i, 8) for i in range(38)]
    Content = claripy.Concat(*symbols)
    state = p.factory.blank_state(
        addr=0x000000000000400ECF,
        #add_options=angr.options.unicorn, #| {angr.options.ZERO_FILL_UNCONSTRAINED_MEMORY},
        remove_options={}
    )

    #@p.hook(0x00000000400EE7, length=0)
    def index(_state):
        print(_state, 'index', _state.regs.esi)
    state.regs.rbp = state.regs.rsp+0x60
    print('ss', state.regs.rbp-0x40)
    state.memory.store(state.regs.rbp-0x40, Content, 38)
    state.memory.store(state.regs.rbp-0x44, 38, 4, endness='Iend_LE')
    simulation = p.factory.simulation_manager(state)
    res = simulation.explore(find=0x0000000400EDB)  # , enable_veritesting=True
    print(len(res.found))
    result = []
    for pp in res.found:
        print('ss', pp.regs.rbp-0x40)
        BV_strCpySrc = pp.memory.load(pp.regs.rbp-0x40, 38)
        pp.solver.add(BV_strCpySrc == dedata)
        if pp.satisfiable():
            tmp = pp.solver.eval(Content, cast_to=bytes)
            print('yes')
            result.append(tmp)
        else:
            print('no')
    return result[0]
if __name__ == "__main__":
    getcrypto=decode2()
    data=[]
    for i in getcrypto:
        data.append(claripy.BVV(i, 8))
    print(data)

    getcrypto = decode3(claripy.Concat(*data))
    data = []
    for i in getcrypto:
        data.append(claripy.BVV(i, 8))
    print(data)

    decode1(claripy.Concat(*data))
