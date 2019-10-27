import sys
import ctypes
import os
from .TriggerBugTypes import *
import pkg_resources
import builtins
_lib_src = ""
if builtins.TriggerBug_Mode == 32:
    _lib_src = r"TriggerBug_32.dll"
elif builtins.TriggerBug_Mode == 64:
    _lib_src = r"TriggerBug_64.dll"
else:
    raise("error builtins.TriggerBug_Mode")
_p = None

if 'develop_mode' in builtins.__dict__ :
    _p = r'C:\Users\bibi\Desktop\TriggerBug\build\src\Engine\Release'+'\\'
    _lib_src = "TriggerBug.dll"
else:
    _p = pkg_resources.resource_filename('TriggerBug','libs')
_retval = os.getcwd()
EngineLib = None
os.chdir(_p)


try:
    EngineLib = ctypes.CDLL(_lib_src)
except Exception as e:
    print(e,'has no %s %s'%(_p, _lib_src))
    sys.exit()
	
os.chdir(_retval)

Super_cb_ctypes = ctypes.CFUNCTYPE(ctypes.py_object, ctypes.py_object)
ijk_call_cb_ctypes = ctypes.CFUNCTYPE(ctypes.c_uint32, StateObj, ctypes.c_uint32)
hook_cb_ctypes = ctypes.CFUNCTYPE(ctypes.c_uint32, StateObj)


EngineLib.TB_Z3_Model_Handle.restype = ctypes.c_void_p
"""
State *		TR_top_state(
	PyObject *base ,
	Super superState_cb, 
	State_Tag(*func_cb)(State *, IRJumpKind),
	char *filename,
	Addr64 oep,
	Bool need_record
)
"""
EngineLib.TB_top_state.argtypes = [ctypes.py_object, Super_cb_ctypes, ijk_call_cb_ctypes, ctypes.c_char_p, ctypes.c_uint64, ctypes.c_char]
EngineLib.TB_top_state.restype = StateObj

"""
PyObject *base, State * father, Addr64 oep
"""
EngineLib.TB_state_fork.argtypes = [ctypes.py_object, StateObj, ctypes.c_uint64]
EngineLib.TB_state_fork.restype = StateObj

EngineLib.TB_cState2pState.argtypes = [StateObj]
EngineLib.TB_cState2pState.restype = ctypes.py_object

EngineLib.TB_state_guest_start.argtypes = [StateObj]
EngineLib.TB_state_guest_start.restype = ctypes.c_uint64

EngineLib.TB_state_guest_start_ep.argtypes = [StateObj]
EngineLib.TB_state_guest_start_ep.restype = ctypes.c_uint64

EngineLib.TB_state_status.argtypes = [StateObj]
EngineLib.TB_state_status.restype = ctypes.c_uint32

EngineLib.TB_state_start.argtypes = [StateObj]

EngineLib.TB_thread_wait.argtypes = []
EngineLib.TB_thread_wait.restype = None

EngineLib.TB_state_delta.argtypes = [StateObj, ctypes.c_int64]

EngineLib.TB_state_compress.argtypes = [StateObj, ctypes.c_uint64, ctypes.c_uint32, ctypes.py_object]

EngineLib.TB_state_branch.argtypes = [StateObj]
EngineLib.TB_state_branch.restype = ctypes.py_object

EngineLib.TB_hook_add.argtypes = [StateObj, ctypes.c_uint64, hook_cb_ctypes]

EngineLib.TB_mem_map.argtypes=[StateObj, ctypes.c_uint64, ctypes.c_uint64]
EngineLib.TB_mem_map.restype=ctypes.c_uint64
EngineLib.TB_mem_unmap.argtypes=[StateObj, ctypes.c_uint64, ctypes.c_uint64]
EngineLib.TB_mem_unmap.restype=ctypes.c_uint64

EngineLib.TB_state_delta.argtypes=[StateObj, ctypes.c_uint64]