from engine.Stateclass import MEMORY_0BJECT
from engine.Syscall.std_system import Std_System

class Des_Manager(MEMORY_0BJECT):
    def __init__(self,state, father_state):
        if hasattr(father_state, 'mem'):
            MEMORY_0BJECT.__init__(self, father_state.des_manager)
        else:
            MEMORY_0BJECT.__init__(self, None)
        self.less_mem[0] = Std_System(state, name='stdin')
        self.less_mem[1] = Std_System(state, name='stdout')
        self.less_mem[2] = Std_System(state, name='stderr')

    def __getitem__(self, item):
        now_obj = self
        while item not in now_obj.less_mem:
            now_obj = now_obj.f_obj
            if not now_obj:
                return False
        if not now_obj.less_mem[item]:
            return False
        return now_obj.less_mem[item]

    def register_obj(self, obj):
        base_description = 3
        while self[base_description]:
            base_description += 1
        self.less_mem[base_description] = obj
        return base_description

    # def __getattr__(self, item):
    #     print('__getattr__',item)
