import logging
import coloredlogs
import xml.dom.minidom as xmldom
import traceback
import capstone

_log = logging.getLogger(name=__name__)
coloredlogs.install(level=logging.INFO, isatty=True,
                    fmt='%(asctime)s %(levelname)-8s %(thread)-6s %(name)s %(message)s',
                    datefmt="%H:%M:%S",
                    level_styles={'debug': {'color': 'green'},
                                  'error': {'color': 'red', 'bold': True, },
                                  },
                    )

from .TriggerBugCore import *
import ctypes

builtins.z3lib = ctypes.CDLL(name="libz3.dll", handle=EngineLib.TB_Z3_Model_Handle())

from .z3 import z3
from .TriggerBugCdll import init_engine_api, TableIdxCallBack
from .TriggerBugConst import *
from .Ijk_call import get_IjkFuns
import archinfo

init_engine_api(EngineLib)

Guest_Arch = None
GuestArchSystem = None
_call_back = {}
tbidx_call_back = {}
_IRJumpKind = {}

def cState2pState(c_obj):
    pState = EngineLib.TB_cState2pState(c_obj)
    if not pState.State_obj:
        pState.State_obj = c_obj
    pState.refresh()
    return pState



class _Context(z3.Context):
    def __init__(self, _ContextObj):
        self.ctx = _ContextObj

    def __del__(self):
        pass


def eval_all(_state, _exp):
    _state.solver.push()
    m_list = []
    re = []
    while True:
        if _state.solver.check() == z3.sat:
            m = _state.solver.model()
            m_list.append(m)
            data = m.eval(_exp)
            z3.Z3_model_inc_ref(m.ctx.ref(), m.model)
            re.append(data)
            _state.solver.add(_exp != data)
        else:
            break
    _state.solver.pop()
    return re


class _Solver(z3.Solver):
    def __init__(self, state, solver, ctx):
        self.state = state
        self.ctx = ctx
        self.backtrack_level = 4000000000
        self.solver = solver

    def add(self, expr, tof = True):
        EngineLib.TB_state_add_assert(self.state.State_obj, expr.ast, tof)

    def __del__(self):
        pass


def _Hook_Server(state_ref):
    s = cState2pState(state_ref)
    pfun, cfun, pass_length = _call_back[s.guest_start]
    if (pass_length):
        EngineLib.TB_state_delta(s.State_obj, pass_length)
    result = pfun(s)
    return result

def _idx2table_Server(state_ref, base, Md):#StateObj, ctypes.c_uint64, z3types.Ast
    s = cState2pState(state_ref)
    d = z3._to_expr_ref(Md, s.ctx)
    c, f = tbidx_call_back[base]
    r = f(s, d)
    if isinstance(r,z3.AstRef):
        z3.Z3_inc_ref(r.ctx.ref(), r.as_ast())
        return r.ast.value
    else:
        raise Exception("error")

def _Ijk_Server(_StateObj, ijk_kind_value):
    pState = cState2pState(_StateObj)
    try:
        c = _IRJumpKind[ijk_kind_value]
        if(c):
            return c(pState, IRJumpKindNmae[ijk_kind_value])
        else:
            _log.error("Unsupported \taddr:%-18x #IRJumpKindNmae: %s #error: method TopState(..., Ijk_unsupport_call is None)", pState.guest_start, IRJumpKindNmae[ijk_kind_value])
            traceback.print_exc()
    except Exception as e:
        _log.error("#unknow error: %s", str(e))
        traceback.print_exc()
        sys.exit()

def _State_Fork(father_obj):
    s = State(father_obj)
    return s

class State(object):
    def __init__(self, father_obj = None):
        self.State_obj = None
        self.guest_start_ep = None
        self.guest_start = None
        self.ctx = None
        self.status = None
        self.solver = None
        self.arch = None
        self.branch = None
        self.f_state = father_obj

    def init(self, _State_obj_types):
        self.State_obj = _State_obj_types
        self.guest_start_ep = EngineLib.TB_state_guest_start_ep(_State_obj_types)
        self.guest_start = EngineLib.TB_state_guest_start(_State_obj_types)
        self.ctx = _Context(EngineLib.TB_state_ctx(_State_obj_types))
        self.status = EngineLib.TB_state_status(_State_obj_types)
        self.solver = _Solver(state=self, solver=EngineLib.TB_state_solver(_State_obj_types), ctx=self.ctx)
        self.arch = Guest_Arch

        self.branch = {}
        self.refresh()

    def refresh(self):
        self.guest_start = EngineLib.TB_state_guest_start(self.State_obj)
        self.guest_start_ep = EngineLib.TB_state_guest_start_ep(self.State_obj)
        self.status = EngineLib.TB_state_status(self.State_obj)
        branch_list = EngineLib.TB_state_branch(self.State_obj)
        self.branch = []
        for state_ref in branch_list:
            ss = StateObj()
            ss.value=state_ref
            _stateObj = EngineLib.TB_cState2pState(ss)
            self.branch.append([_stateObj.guest_start_ep, _stateObj])

    def hook_add(self, Address, callBackFunc, length=0):
        cb = ctypes.cast(hook_cb_ctypes(_Hook_Server), hook_cb_ctypes)
        _call_back[Address] = [callBackFunc, cb, length]
        EngineLib.TB_hook_add(self.State_obj, Address, cb)

    def TB_state_delta(self, pass_length):
        EngineLib.TB_state_delta(self.State_obj, pass_length)

    def mem_write(self, address, value, size):
        if (type(address) == int):
            if (type(value) == int):
                if (size == 1):
                    EngineLib.mem_r_r_write1(self.State_obj, address, value)
                elif (size == 2):
                    EngineLib.mem_r_r_write2(self.State_obj, address, value)
                elif (size == 4):
                    EngineLib.mem_r_r_write4(self.State_obj, address, value)
                elif (size == 8):
                    EngineLib.mem_r_r_write8(self.State_obj, address, value)
                else:
                    raise ("err size")
            else:
                value = value.ast
                if (size == 1):
                    EngineLib.mem_r_s_write1(self.State_obj, address, value)
                elif (size == 2):
                    EngineLib.mem_r_s_write2(self.State_obj, address, value)
                elif (size == 4):
                    EngineLib.mem_r_s_write4(self.State_obj, address, value)
                elif (size == 8):
                    EngineLib.mem_r_s_write8(self.State_obj, address, value)
                else:
                    raise ("err size")
        else:
            if (type(value) == int):
                address = address.ast
                if (size == 1):
                    EngineLib.mem_s_r_write1(self.State_obj, address, value)
                elif (size == 2):
                    EngineLib.mem_s_r_write2(self.State_obj, address, value)
                elif (size == 4):
                    EngineLib.mem_s_r_write4(self.State_obj, address, value)
                elif (size == 8):
                    EngineLib.mem_s_r_write8(self.State_obj, address, value)
                else:
                    raise ("err size")
            else:
                address = address.ast
                value = value.ast
                if (size == 1):
                    EngineLib.mem_s_s_write1(self.State_obj, address, value)
                elif (size == 2):
                    EngineLib.mem_s_s_write2(self.State_obj, address, value)
                elif (size == 4):
                    EngineLib.mem_s_s_write4(self.State_obj, address, value)
                elif (size == 8):
                    EngineLib.mem_s_s_write8(self.State_obj, address, value)
                else:
                    raise ("err size")

    def mem_read(self, address, size):
        ast = None
        real = None
        if (type(address) == int):
            if (size == 1):
                real = ctypes.c_uint8()
                ast = EngineLib.mem_r_read1(self.State_obj, real, address)
            elif (size == 2):
                real = ctypes.c_uint16()
                ast = EngineLib.mem_r_read2(self.State_obj, real, address)
            elif (size == 4):
                real = ctypes.c_uint32()
                ast = EngineLib.mem_r_read4(self.State_obj, real, address)
            elif (size == 8):
                real = ctypes.c_uint64()
                ast = EngineLib.mem_r_read8(self.State_obj, real, address)
            else:
                raise ("err size")
        else:
            addr = address.ast
            if (size == 1):
                real = ctypes.c_uint8()
                ast = EngineLib.mem_s_read1(self.State_obj, real, addr)
            elif (size == 2):
                real = ctypes.c_uint16()
                ast = EngineLib.mem_s_read2(self.State_obj, real, addr)
            elif (size == 4):
                real = ctypes.c_uint32()
                ast = EngineLib.mem_s_read4(self.State_obj, real, addr)
            elif (size == 8):
                real = ctypes.c_uint64()
                ast = EngineLib.mem_s_read8(self.State_obj, real, addr)
            else:
                raise ("err size")

        if (ast.value == None):
            return real.value
        else:
            return z3._to_expr_ref(ast, self.ctx)

    def mem_r(self, address, size):
        return self.mem_read(address, size)

    def mem_w(self, address, value, size):
        self.mem_write(address, value, size)

    def mem_unmap(self, address, end):
        length = end - address
        err = EngineLib.mem_unmap(self.State_obj, address, address + length)
        if err:
            _log.error("mem_unmap :%18x length: %10x has mapped at at %-18x", address, length, err)

    def mem_map(self, address, end):
        length = end - address
        err = EngineLib.mem_map(self.State_obj, address, address + length)
        if err:
            _log.warning("mem_map :%18x length: %10x has mapped at at %-18x", address, length, address + length - err)

    def regs_write(self, regName, value):
        global Guest_Arch
        offset, n_bytes = Guest_Arch.registers[regName]
        if (type(value) == int):
            if (n_bytes == 1):
                EngineLib.regs_r_write1(self.State_obj, offset, value)
            elif (n_bytes == 2):
                EngineLib.regs_r_write2(self.State_obj, offset, value)
            elif (n_bytes == 4):
                EngineLib.regs_r_write4(self.State_obj, offset, value)
            elif (n_bytes == 8):
                EngineLib.regs_r_write8(self.State_obj, offset, value)
            else:
                raise ("err size")
        else:
            value = value.ast
            if (n_bytes == 1):
                EngineLib.regs_s_write1(self.State_obj, offset, value)
            elif (n_bytes == 2):
                EngineLib.regs_s_write2(self.State_obj, offset, value)
            elif (n_bytes == 4):
                EngineLib.regs_s_write4(self.State_obj, offset, value)
            elif (n_bytes == 8):
                EngineLib.regs_s_write8(self.State_obj, offset, value)
            else:
                raise ("err size")
        pass

    def regs_read(self, regName):
        global Guest_Arch
        offset, n_bytes = Guest_Arch.registers[regName]
        ast = None
        real = None
        if (n_bytes == 1):
            real = ctypes.c_uint8()
            ast = EngineLib.regs_read1(self.State_obj, real, offset)
        elif (n_bytes == 2):
            real = ctypes.c_uint16()
            ast = EngineLib.regs_read2(self.State_obj, real, offset)
        elif (n_bytes == 4):
            real = ctypes.c_uint32()
            ast = EngineLib.regs_read4(self.State_obj, real, offset)
        elif (n_bytes == 8):
            real = ctypes.c_uint64()
            ast = EngineLib.regs_read8(self.State_obj, real, offset)
        else:
            raise ("err size")
        if (ast.value == None):
            return real.value
        else:
            return z3._to_expr_ref(ast, self.ctx)

    def regs_r(self, regName):
        return self.regs_read(regName)

    def regs_w(self, regName, value):
        self.regs_write(regName, value)

    def reg_r(self, regName):
        return self.regs_read(regName)

    def reg_w(self, regName, value):
        self.regs_write(regName, value)

    def go(self):
        EngineLib.TB_state_start(self.State_obj)
        self.refresh()

    def wait(self):
        EngineLib.TB_thread_wait()

    def compress(self, address, State_Flag, avoid_State_flags):
        if not isinstance(avoid_State_flags, list):
            if isinstance(avoid_State_flags, tuple):
                avoid_State_flags = list(avoid_State_flags)
            elif isinstance(avoid_State_flags, int):
                avoid_State_flags = [avoid_State_flags]
            else:
                raise Exception("?????????")
        EngineLib.TB_state_compress(self.State_obj, address, State_Flag, avoid_State_flags)
        self.refresh()

    def add(self, Z3assert, ToF):
        EngineLib.TB_state_add_assert(self.State_obj, Z3assert.ast, ToF)


    def __getattr__(self, name):
        global Guest_Arch
        if name in Guest_Arch.registers:
            return self.regs_read(name)
        else:
            raise AttributeError(name)

    def __str__(self):
        self.refresh()
        child_str = ''
        for oep, state in self.branch:
            child_str += str(state).replace('\n', '\n\t')
        if child_str == '':
            child_str = 'Arrival target'
        if self.status in State_Tag:
            return '#entry:{:x} #ip:{:x} Status:{:s} #child{{\n\t{:s}\n}}\n'.format(self.guest_start_ep,
                                                                                    self.guest_start,
                                                                                    State_Tag[self.status], child_str)
        else:
            return '#entry:{:x} #ip:{:x} Status:userDef{:d} #child{{\n\t{:s}\n}}\n'.format(self.guest_start_ep,
                                                                                           self.guest_start,
                                                                                           self.status, child_str)

    def Disasm(self, n_code):
        buff = []
        cs = self.arch.capstone
        count = 0
        while True:
            i = self.mem_r(self.guest_start + count * 8, 8)
            buff += i.to_bytes(8, byteorder='little')

            all_insn = capstone.ctypes.POINTER(capstone._cs_insn)()
            code = bytes(buff)
            insns = []
            res = capstone._cs.cs_disasm(cs.csh, code, len(code), self.guest_start, 1, capstone.ctypes.byref(all_insn))
            if (res >= n_code):
                for i in range(res):
                    insns.append(capstone.CsInsn(cs, all_insn[i]))
                return (insns,buff[:count*8-8 + insns[-1].size])
            count += 1

    def asm(self, codestr):
        ks = self.arch.keystone
        return ks.asm(codestr)

_Ijk_Server_cb = None
_State_Fork_cb = None

def TopState(file_name=b'./TriggerBug.xml', need_record=False, oep=0, Ijk_unsupport_call=None,
             Ijk_hook_call=None):
    global Guest_Arch, GuestArchSystem
    global _Ijk_Server_cb
    global _State_Fork_cb
    DOMTree = xmldom.parse(file_name)
    TriggerBugNode = DOMTree.getElementsByTagName("TriggerBug")[0]
    VexArchValue = int(TriggerBugNode.getElementsByTagName("VexArch")[0].firstChild.data, 16)
    GuestArchSystem = TriggerBugNode.getElementsByTagName("VexArchSystem")[0].firstChild.data
    if (GuestArchSystem.find("win") != -1):
        GuestArchSystem = 'windows'
    assert GuestArchSystem in ['windows', 'linux']
    for v in VexArch:
        if (VexArch[v] == VexArchValue):
            if (hasattr(archinfo, v[3:])):
                re = getattr(archinfo, v[3:])
                Guest_Arch = re()
            break
    if (type(file_name) == str):
        file_name = bytes(file_name, encoding='utf-8')
    if(Ijk_unsupport_call):
        Ijk_hook_call=None
    IjkFuns = get_IjkFuns()
    for _ijkoffset in IRJumpKindNmae:
        ijkname = IRJumpKindNmae[_ijkoffset]
        if Ijk_hook_call:
            _IRJumpKind[_ijkoffset] = Ijk_hook_call
        else:
            if(IjkFuns):
                if ijkname in IjkFuns:
                    _IRJumpKind[_ijkoffset] = IjkFuns[ijkname]
                else:
                    _IRJumpKind[_ijkoffset] = Ijk_unsupport_call
    _Ijk_Server_cb = ctypes.cast(ijk_call_cb_ctypes(_Ijk_Server), ijk_call_cb_ctypes)
    _State_Fork_cb = ctypes.cast(Super_cb_ctypes(_State_Fork), Super_cb_ctypes)
    state = State()
    cState = EngineLib.TB_top_state(state,
                                    _State_Fork_cb,
                                    _Ijk_Server_cb,
                                    file_name,
                                    oep,
                                    need_record
                                    )
    state.init(cState)
    return state

def idx2table_add(ma_base, func):
    __idx2table_cb = ctypes.cast(TableIdxCallBack(_idx2table_Server), TableIdxCallBack)
    tbidx_call_back[ma_base] = [__idx2table_cb, func]
    EngineLib.TB_idx2tableValueDecl_add(ma_base, __idx2table_cb)