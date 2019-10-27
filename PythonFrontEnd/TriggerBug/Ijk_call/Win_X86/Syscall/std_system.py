
class Std_System():
    def __init__(self, state, name):
        self.state = state
        self.buff = []
        self.name = name

    def write(self, state):
        rsi = state.reg_r('rsi').args[0]
        rdx = state.reg_r('rdx').args[0]
        self.buff += state.mem_r(rsi, rdx).chop(8)
        return rdx

    def read(self, state):
        rsi = state.reg_r('rsi').args[0]
        rdx = state.reg_r('rdx').args[0]
        length=rdx
        p = self.state.stdin_point
        symbolic=[]
        if len(self.state.stdin) - p - rdx < 0:
            symbolic=[self.state.solver.BVS("sym%d"%_ ,8)for _ in range(rdx - len(self.state.stdin) + p)]
            rdx = len(self.state.stdin) - p
        self.state.stdin_point += rdx
        p = self.state.stdin_point
        re= [_ for _ in self.state.stdin[p - rdx:p]]+symbolic
        state.mem_w(rsi,re)
        self.buff+=re
        return length
