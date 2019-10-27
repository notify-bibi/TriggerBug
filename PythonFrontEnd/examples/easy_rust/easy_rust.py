# coding:utf-8
import archinfo
import builtins

builtins.develop_mode = True
builtins.TriggerBug_Mode = 64
import ctypes
import TriggerBug
import TriggerBug.z3 as z3

top_state = TriggerBug.TopState(
    file_name = r'./easy_rust.xml',
    need_record = True,
    # 在需要合并(compress)state时，必须要保证被compress 的state对象的need_record=True，否则会报错，因为need_record=False的state是不会记录子state生命周期中所产生的修改,继而无法合并
    oep = 0,
    Ijk_unsupport_call = None,  # if set,Ir jump kind call what I not support will call this func
    Ijk_hook_call = None  # if set, all the Ir jump kind call will call this func
)
flag=[]
for i in range(24):
    k = z3.BitVec("flag%d" % i, 8, top_state.ctx)
    flag.append(k)
    #top_state.add(z3.And(z3.UGT(k, 5), z3.ULE(k, 128), top_state.ctx), True)
    #top_state.mem_w(top_state.ebp - 0x60 + i, k, 1)

#top_state.mem_w(top_state.rbp - 0x60 + 24, 0, 1)




def evalvalue(_state = TriggerBug.State):
    global flag
    for i in range(7):
        _state.add(_state.mem_r(_state.rdx + i*4, 4)== _state.mem_r(_state.rcx + i*4, 4), True)
    _state.add(_state.mem_r(_state.rdx + 28, 2)== _state.mem_r(_state.rcx + 28, 2), True)
    print("check")
    if _state.solver.check()==z3.sat:
        m = _state.solver.model()
        print(m)
        flagv = int(str(m.eval(z3.Concat(*flag))) )
        print(flagv.to_bytes(28, byteorder='big'))
    else:
        print("unsat")

    return TriggerBug.Death

def strlen(_state):
    _state.reg_w("rax",0x0000000000000018)
    return TriggerBug.Running


#/* The D flag is stored here, encoded as either -1 or +1 */
top_state.reg_w("d",0x1)
#top_state.hook_add(0x0000401A8B, strlen, length=5)
#top_state.hook_add(0x0000401AAC, strlen, length=5)

#top_state.hook_add(0x000401AD9, evalvalue)

top_state.go()
top_state.wait()
print(top_state)
