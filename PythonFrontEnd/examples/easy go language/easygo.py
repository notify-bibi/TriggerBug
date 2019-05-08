# u need patch the ./Engine/TriggerBugCore.py
# p=r"C:\Users\bibi\Desktop\TriggerBug\build\src\Engine\Release"
# to
# your dll(libz3.dll and TriggerBug.dll) path 

from TriggerBug import *
import TriggerBug.z3




def decode2():
    de=[]

    args = ['rdi','rsi','rdx','rcx','r8']
    def chk2(_state):
        gh=_state.dh
        re=eval_all(_state, gh)
        print("success    ",  re )
        return Running

    def evalvalue(_state):
        addr=_state.rdi
        _state.solver.push()
        for i,v in enumerate(c):
            val=_state.mem_r(addr+i,1)
            if(type(val)==int):
                print(val)
                if(val!=v):
                    return Death
            else:
                _state.solver.add(val==v)
        if (_state.solver.check()==z3.sat):
            m=_state.solver.model()
            print("success    ")

            for a in args:
                k = z3.BitVec(a, 64, state.ctx)
                de.append(m.eval(k).as_long())
            _state.solver.pop()
            return Death
        else:
            print("faild    ")
            _state.solver.pop()
            return Death


    state=TopState(file_name=r'C:\Users\bibi\Desktop\\TriggerBug.xml',need_record=True,oep=0x0004015B8)

    # state.mem_write(0x7ffff7dec7b8,0x90909090,4)
    # state.mem_write(0x7ffff7dec7b8+4,0x90,1)
    # state.mem_write(0x7FFFF7DEC7D4,0x90909090,4)
    # state.mem_write(0x7FFFF7DEC7D4+4,0x90,1)
    #
    # arg0 = state.rdi
    # arg1 = state.rsi
    # arg2 = state.rdx
    # arg3 = state.rcx
    # arg4 = state.r8
    #
    # for i,a in enumerate(args):
    #     k = z3.BitVec(a, 64, state.ctx)
    #     state.add(z3.UGT(k, 0) , True)
    #     state.regs_write(a, k)
    #     if(i<4):
    #         index=state.mem_r(state.rbp - 0x148,1)
    #         addr=state.rbp-0x140+(index+i)*8
    #         state.mem_w(addr,k,8)

    state.go()
    print(state)

    return  de
dec2=None
if 1:
    dec2 = decode2()
else:
    dec2=[288230377917403225, 1152921508689107638, 17594813653004, 70372930466384, 382056768]


#
#
#
#
#
#
#
#
#
# def faild(_state):
#     return Death
#
# def fcmp(_state):
#     return 88
#
# def cmp2(_state):
#     return 99
#
# flagcount=0
#
# m=None
# def success(_state):
#     global m
#     print(_state.solver.check())
#     m=_state.solver.model()
#     print(m)
#     return 100
#
# addr=None
#
#
# def IDIV(_state):
#     d=_state.rax // _state.ecx
#     m=_state.rax % _state.ecx
#     _state.regs_write('rax',d)
#     _state.regs_write('rdx',m)
#     return 99
#
# def sprintf(_state):
#     value=_state.edx
#     print("sprintf",value)
#     saddr=_state.rdi
#     hi=z3.ZeroExt(4,z3.Extract(7,4,value))
#     hi=z3.If(hi<10,hi +ord('0'),hi+(ord('A')-10),_state.ctx)
#
#
#     lo=z3.ZeroExt(4,z3.Extract(3,0,value))
#     lo=z3.If(lo<10,lo +ord('0'),lo+(ord('A')-10),_state.ctx)
#     _state.mem_w(saddr,lo,1)
#     _state.mem_w(saddr+1, hi, 1)
#     return Running
# def strlen(_state):
#     _state.reg_w('rax',16*2)
#     return Running
#
#
#
# def strcmp(_state):
#     c=b'RVYtG85NQ9OPHU4uQ8AuFM+MHVVrFMJMR8FuF8WJQ8Y='
#     addr=_state.rdi
#     _state.solver.push()
#     for i,v in enumerate(c):
#         val=_state.mem_r(addr+i,1)
#
#         if(type(val)==int):
#             if(val!=v):
#                 return Death
#         else:
#             print(type(val),chr(val.as_long()), chr(v))
#             _state.solver.add(val==v)
#     if (_state.solver.check()==z3.sat):
#         m=_state.solver.model()
#         print("success    ",m)
#         _state.solver.pop()
#         return Running
#     else:
#         print("faild    ")
#         _state.solver.pop()
#         return Death
#
#
# # sss=z3.BitVec("flag", 8, state.ctx )
# # state.regs_write("al",sss)
# # fg=state.regs_read("al")
# # del fg
# # ssjk=state.rbp-0x40
#
#
# addr=state.rbp-0x80
#
# n=8
# for i in range(n):
#     k=z3.BitVec('flag_%d' % (i+50), 8, state.ctx)
#     so1=z3.And( k >= ord("A"), k <= ord("Z"),state.ctx)
#     so2=z3.And( k >= ord("a"), k <= ord("z"), state.ctx)
#     so3=z3.And( k >= ord("0"), k <= ord("9"), state.ctx)
#     state.add(z3.Or(so1, so2,so3,state.ctx) == True, True)
#     state.mem_write(addr+i,k,1)
#
#
#
#
#
# state.hook_add(0X0406B24  ,success)
# state.hook_add(0X0406B3A   ,faild)
#
# state.hook_add(0x4066EB     ,fcmp)
#
#
# def chk(_state):
#     dl=_state.dl
#     saddr=_state.rbp-0x70
#     for m in range(20):
#         print("check",z3.simplify(_state.mem_r(saddr+m,1)))
#     # print("check", _state.rax,z3.simplify(dl))
#     # _state.mem_w(_state.rax,_state.dl,1)
#     return Running
#
#
# #
# # state.mem_write(0x0000401938 ,0x9090   ,2)
# # state.hook_add(0x00004069E2   ,chk)
# #
#
#
#
#
# state.hook_add(0x0040680C    ,sprintf)
# state.mem_write(0x00406969 ,0x90909090   ,4)
# state.mem_write(0x00406969+4 ,0x90   ,1)
#
# state.hook_add(0x0000406AAC     ,strlen)
#
# state.hook_add(0x04067A7   ,cmp2)
#
# # state.hook_add(0x000040954E       ,okk)
# # # state.hook_add(0x00435087 ,IDIV)
# #
# # print(state.mem_w(5019890,7,1))
#
# def getNewState(_state):
#     if(_state.branch):
#         return False
#     for i in _state.branch:
#         if i.status==Fork:
#             if(getNewState(i)):
#                 return True
#     return False
#
#
#
# stateGo(state)
#
#
# for i in range(7):
#     stateGo(state)
#     print(i,state)
#     state.compress(0x004066EB,88,[Death])
#     print(i,state)
#
# stateGo(state)
# print(state)
# state.compress(0x04067A7,99,[Death])
# print(state)
#
# stateGo(state)
# print(state)
#
# #
# # while True:
# #     stateGo(state)
# #     print(state)
# #     if(state.status==Death):
# #         break
# #     elif state.status==Fork:
# #         print('fork')
# #     if state.branch:
# #         state.compress(0x00406A75,88,[Death])
# #         print(state.rax)
# #         if(isinstance(state.rax,z3.ExprRef)):
# #             rax=z3.simplify(state.rax)
# #             print(rax)
# #             re=eval_all(state,rax)
# #             print(re)
# #         if state.status == Fork:
# #             print('fork')
# #             state=getNewState(state)
#
#
# #print(state)
# # state.compress(0x00400ECD,100,[Death])
# #print(state,addr)
# # state=state.branch[0x400ecd]
# #state.hook_add(0x00400ECD  ,nasjk)
# print(m)