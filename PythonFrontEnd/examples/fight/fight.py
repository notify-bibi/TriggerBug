# coding:utf-8
import archinfo
import builtins
import sys

"""
mov eax, dword ptr [esp-0x24]
mov     [esp+0x104], eax
lea      eax,dword ptr [esp+0x104]
mov     [esp+4], eax
mov     dword ptr [esp], offset dword_488140
mov     dword ptr [ebp-0x58], 1
call    Print
"""
builtins.develop_mode = True
builtins.TriggerBug_Mode = 32
import ctypes
import TriggerBug
import TriggerBug.z3 as z3

top_state = TriggerBug.TopState(
    file_name = r'./fight.xml',
    need_record = True,
    # 在需要合并(compress)state时，必须要保证被compress 的state对象的need_record=True，否则会报错，因为need_record=False的state是不会记录子state生命周期中所产生的修改,继而无法合并
    oep = 0,
    Ijk_unsupport_call = None,  # if set,Ir jump kind call what I not support will call this func
    Ijk_hook_call = None  # if set, all the Ir jump kind call will call this func
)
flag=[]

for i in range(420):
    k = z3.BitVec("C%d" % i, 32, top_state.ctx)
    flag.append(k)
    top_state.add(z3.ULE(k, 4), True)
    top_state.mem_w(0x0BE33D4 + i*4, k, 4)




def evalvalue(_state = TriggerBug.State):
    global flag
    # for i in range(7):
    #     _state.add(_state.mem_r(_state.rdx + i*4, 4)== _state.mem_r(_state.rcx + i*4, 4), True)
    print("check")
    if _state.solver.check()==z3.sat:
        m = _state.solver.model()
        data=0
        for i in flag:
            flagv=None
            try:
                flagv = int(str(m.eval(z3.Concat(*(flag[:-3])))))
            except Exception as e:
                break
            data=(data<<2)|flagv
        print(data.to_bytes(28, byteorder='little'))
    else:
        print("unsat")

    return TriggerBug.Death

def strlen(_state):
    _state.reg_w("rax",0x0000000000000018)
    return TriggerBug.Running



def compress(_statte):
    v = _statte.mem_r( _statte.ebp - 0x1c, 4)
    if v==5:
        return 2333
    elif v==100:
        evalvalue(_statte)
    else:
        return TriggerBug.Running

def cmp(_state):
    if(_state.al==0):
        print("faild")
        return TriggerBug.Death
    else:
        evalvalue(_state)
        return TriggerBug.Running

top_state.reg_w("d",0x1)
top_state.hook_add(0x00401E02, cmp, length=0)
top_state.hook_add(0x00401DF4, compress, length=0)

#top_state.hook_add(0x00401DEE, compress, length=0)


for i in range(0x8c*3):
    top_state.go()
    top_state.wait()

    if top_state.branch:
        top_state.compress(0x00401DF4,2333,[TriggerBug.Death])
        top_state=top_state.branch[-1][1]
        if isinstance(top_state,list):
            print(top_state)
top_state.go()
top_state.wait()

print(top_state)
