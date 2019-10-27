from .z3 import z3types
from .TriggerBugTypes import StateObj
from .TriggerBugCore import ctypes

TableIdxCallBack = ctypes.CFUNCTYPE(z3types.Ast, StateObj, ctypes.c_uint64, z3types.Ast)

def init_engine_api(EngineLib):
    EngineLib.TB_idx2tableValueDecl_add.argtypes = [ctypes.c_uint64, TableIdxCallBack]

    EngineLib.TB_state_ctx.argtypes = [StateObj]
    EngineLib.TB_state_ctx.restype = z3types.ContextObj

    EngineLib.TB_state_solver.argtypes = [StateObj]
    EngineLib.TB_state_solver.restype = z3types.SolverObj

    EngineLib.TB_state_add_assert.argtypes = [StateObj, z3types.Ast, ctypes.c_char]

    EngineLib.regs_r_write1.argtypes = [StateObj, ctypes.c_uint16, ctypes.c_uint8]
    EngineLib.regs_r_write2.argtypes = [StateObj, ctypes.c_uint16, ctypes.c_uint16]
    EngineLib.regs_r_write4.argtypes = [StateObj, ctypes.c_uint16, ctypes.c_uint32]
    EngineLib.regs_r_write8.argtypes = [StateObj, ctypes.c_uint16, ctypes.c_uint64]

    EngineLib.regs_s_write.argtypes = [StateObj, ctypes.c_uint16, z3types.Ast]
    EngineLib.regs_s_write1.argtypes = [StateObj, ctypes.c_uint16, z3types.Ast]
    EngineLib.regs_s_write2.argtypes = [StateObj, ctypes.c_uint16, z3types.Ast]
    EngineLib.regs_s_write4.argtypes = [StateObj, ctypes.c_uint16, z3types.Ast]
    EngineLib.regs_s_write8.argtypes = [StateObj, ctypes.c_uint16, z3types.Ast]

    EngineLib.regs_read1.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint8), ctypes.c_uint16]
    EngineLib.regs_read2.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint16), ctypes.c_uint16]
    EngineLib.regs_read4.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint32), ctypes.c_uint16]
    EngineLib.regs_read8.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint64), ctypes.c_uint16]
    EngineLib.regs_read1.restype = z3types.Ast
    EngineLib.regs_read2.restype = z3types.Ast
    EngineLib.regs_read4.restype = z3types.Ast
    EngineLib.regs_read8.restype = z3types.Ast

    EngineLib.mem_r_r_write1.argtypes = [StateObj, ctypes.c_uint64, ctypes.c_uint8]
    EngineLib.mem_r_r_write2.argtypes = [StateObj, ctypes.c_uint64, ctypes.c_uint16]
    EngineLib.mem_r_r_write4.argtypes = [StateObj, ctypes.c_uint64, ctypes.c_uint32]
    EngineLib.mem_r_r_write8.argtypes = [StateObj, ctypes.c_uint64, ctypes.c_uint64]

    EngineLib.mem_r_s_write1.argtypes = [StateObj, ctypes.c_uint64, z3types.Ast]
    EngineLib.mem_r_s_write2.argtypes = [StateObj, ctypes.c_uint64, z3types.Ast]
    EngineLib.mem_r_s_write4.argtypes = [StateObj, ctypes.c_uint64, z3types.Ast]
    EngineLib.mem_r_s_write8.argtypes = [StateObj, ctypes.c_uint64, z3types.Ast]

    EngineLib.mem_s_r_write1.argtypes = [StateObj, z3types.Ast, ctypes.c_uint8]
    EngineLib.mem_s_r_write2.argtypes = [StateObj, z3types.Ast, ctypes.c_uint16]
    EngineLib.mem_s_r_write4.argtypes = [StateObj, z3types.Ast, ctypes.c_uint32]
    EngineLib.mem_s_r_write8.argtypes = [StateObj, z3types.Ast, ctypes.c_uint64]

    EngineLib.mem_s_s_write1.argtypes = [StateObj, z3types.Ast, z3types.Ast];
    EngineLib.mem_s_s_write2.argtypes = [StateObj, z3types.Ast, z3types.Ast];
    EngineLib.mem_s_s_write4.argtypes = [StateObj, z3types.Ast, z3types.Ast];
    EngineLib.mem_s_s_write8.argtypes = [StateObj, z3types.Ast, z3types.Ast];

    EngineLib.mem_r_read1.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint8),  ctypes.c_uint64]
    EngineLib.mem_r_read2.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint16), ctypes.c_uint64]
    EngineLib.mem_r_read4.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint32), ctypes.c_uint64]
    EngineLib.mem_r_read8.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint64), ctypes.c_uint64]
    EngineLib.mem_r_read1.restype = z3types.Ast
    EngineLib.mem_r_read2.restype = z3types.Ast
    EngineLib.mem_r_read4.restype = z3types.Ast
    EngineLib.mem_r_read8.restype = z3types.Ast

    EngineLib.mem_s_read1.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint8), z3types.Ast]
    EngineLib.mem_s_read2.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint16), z3types.Ast]
    EngineLib.mem_s_read4.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint32), z3types.Ast]
    EngineLib.mem_s_read8.argtypes = [StateObj, ctypes.POINTER(ctypes.c_uint64), z3types.Ast]
    EngineLib.mem_s_read1.restype = z3types.Ast
    EngineLib.mem_s_read2.restype = z3types.Ast
    EngineLib.mem_s_read4.restype = z3types.Ast
    EngineLib.mem_s_read8.restype = z3types.Ast
