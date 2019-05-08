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
import builtins
import ctypes

builtins.z3lib = ctypes.CDLL(name="libz3.dll", handle=EngineLib.Z3_Model_Handle())
from .z3 import z3
from .TriggerBugCdll import init_engine_api
from .TriggerBugConst import *
from .Ijk_call import get_IjkFuns
import archinfo

init_engine_api(EngineLib)

Guest_Arch = None
GuestArchSystem = None
_call_back = {}
_IRJumpKind = {}


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

    def add(self, expr):
        EngineLib.state_add_assert(self.state.State_obj, expr.ast, True)

    def __del__(self):
        pass


def _Hook_Server(state_ref):
    _stateObj = StateObj(state_ref)
    _stateObj.value = state_ref
    s = State(_stateObj)
    pfun, cfun, pass_length = _call_back[s.guest_start]
    if (pass_length):
        EngineLib.hook_pass_code(s.State_obj, pass_length)
    result = pfun(s)
    return result


def _Ijk_Server(state_ref, ijk_kind_value):
    _stateObj = StateObj(state_ref)
    _stateObj.value = state_ref
    s = State(_stateObj)
    try:
        c = _IRJumpKind[ijk_kind_value]
        if(c):
            return c(s, IRJumpKindNmae[ijk_kind_value])
        else:
            _log.error("Unsupported \taddr:%-18x #IRJumpKindNmae: %s #error: method TopState(..., Ijk_unsupport_call is None)", s.guest_start, IRJumpKindNmae[ijk_kind_value])
            traceback.print_exc()
    except Exception as e:
        _log.error("#unknow error: %s", str(e))
        traceback.print_exc()
        sys.exit()


class State(object):
    def __init__(self, _State_obj_types):
        self.State_obj = _State_obj_types
        self.guest_start_ep = EngineLib.state_guest_start_ep(_State_obj_types)
        self.guest_start = EngineLib.state_guest_start(_State_obj_types)
        self.ctx = _Context(EngineLib.StateCtx(_State_obj_types))
        self.status = EngineLib.state_status(_State_obj_types)
        self.solver = _Solver(state=self, solver=EngineLib.state_solver(_State_obj_types), ctx=self.ctx)
        self.arch = Guest_Arch

        self.branch = {}
        self.refresh()

    def refresh(self):
        self.guest_start = EngineLib.state_guest_start(self.State_obj)
        self.status = EngineLib.state_status(self.State_obj)
        branch_list = EngineLib.stateBranch(self.State_obj)
        branchSize = len(branch_list)
        branchArr = None
        self.branch = []
        for state_ref in branch_list:
            _stateObj = StateObj(state_ref)
            _stateObj.value = state_ref
            s = State(_stateObj)
            self.branch.append([s.guest_start_ep, s])

    def hook_add(self, Address, callBackFunc, length=0):
        cb = ctypes.cast(callback_ctypes(_Hook_Server), callback_ctypes)
        _call_back[Address] = [callBackFunc, cb, length]
        EngineLib.hook_add(self.State_obj, Address, cb)

    def hook_pass_code(self, pass_length):
        EngineLib.hook_pass_code(self.State_obj, pass_length)

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
            address = address.ast
            if (size == 1):
                real = ctypes.c_uint8()
                ast = EngineLib.mem_s_read1(self.State_obj, real, address)
            elif (size == 2):
                real = ctypes.c_uint16()
                ast = EngineLib.mem_s_read2(self.State_obj, real, address)
            elif (size == 4):
                real = ctypes.c_uint32()
                ast = EngineLib.mem_s_read4(self.State_obj, real, address)
            elif (size == 8):
                real = ctypes.c_uint64()
                ast = EngineLib.mem_s_read8(self.State_obj, real, address)
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
        EngineLib.state_go(self.State_obj)
        self.refresh()

    def compress(self, address, State_Flag, avoid_State_flags):
        if not isinstance(avoid_State_flags, list):
            if isinstance(avoid_State_flags, tuple):
                avoid_State_flags = list(avoid_State_flags)
            elif isinstance(avoid_State_flags, int):
                avoid_State_flags = [avoid_State_flags]
            else:
                raise Exception("?????????")
        EngineLib.state_compress(self.State_obj, address, State_Flag, avoid_State_flags)
        self.refresh()

    def add(self, Z3assert, ToF):
        EngineLib.state_add_assert(self.State_obj, Z3assert.ast, ToF)

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
                return insns
            count += 1


Ijk_Server_cb = None


def TopState(file_name=b'./TriggerBug.xml', need_record=False, oep=0, Ijk_unsupport_call=None,
             Ijk_hook_call=None):
    global Guest_Arch, GuestArchSystem
    global Ijk_Server_cb
    Ijk_Server_cb = ctypes.cast(ijk_callback_ctypes(_Ijk_Server), ijk_callback_ctypes)
    EngineLib.init_Ijk_call_back(Ijk_Server_cb)

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
    for _ijkoffset in IRJumpKindNmae:
        ijkname = IRJumpKindNmae[_ijkoffset]
        IjkFuns = get_IjkFuns()
        if Ijk_hook_call:
            _IRJumpKind[_ijkoffset] = Ijk_hook_call
        else:
            if ijkname in IjkFuns:
                _IRJumpKind[_ijkoffset] = IjkFuns[ijkname]
            else:
                _IRJumpKind[_ijkoffset] = Ijk_unsupport_call
    state = EngineLib.new_state(file_name, 0, need_record)

    return State(state)

