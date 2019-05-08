import sys
import ctypes
import os
from .TriggerBugTypes import *
import pkg_resources
_lib_src = r"TriggerBug.dll"
_p = pkg_resources.resource_filename('TriggerBug','TriggerBug/lib')
_retval = os.getcwd()
EngineLib = None
os.chdir(_p)


try:
    EngineLib = ctypes.CDLL(_lib_src)
except Exception as e:
    print(e,'has no %s %s'%(_p,_lib_src))
    sys.exit()
	
os.chdir(_retval)

EngineLib.Z3_Model_Handle.restype = ctypes.c_void_p

EngineLib.new_state.argtypes = [ctypes.c_char_p, ctypes.c_uint64, ctypes.c_char]
EngineLib.new_state.restype = StateObj

EngineLib.new_state_fork.argtypes = [StateObj, ctypes.c_uint64]
EngineLib.new_state_fork.restype = StateObj

EngineLib.state_go.argtypes = [StateObj]
EngineLib.hook_pass_code.argtypes = [StateObj, ctypes.c_int64]
EngineLib.state_compress.argtypes = [StateObj, ctypes.c_uint64, ctypes.c_uint32, ctypes.py_object]

EngineLib.state_guest_start.argtypes = [StateObj]
EngineLib.state_guest_start.restype = ctypes.c_uint64

EngineLib.state_guest_start_ep.argtypes = [StateObj]
EngineLib.state_guest_start_ep.restype = ctypes.c_uint64

EngineLib.state_status.argtypes = [StateObj]
EngineLib.state_status.restype = ctypes.c_uint32

callback_ctypes = ctypes.CFUNCTYPE(ctypes.c_uint32, ctypes.c_void_p)
ijk_callback_ctypes = ctypes.CFUNCTYPE(ctypes.c_uint32, ctypes.c_void_p, ctypes.c_uint32)
EngineLib.hook_add.argtypes = [StateObj, ctypes.c_uint64, callback_ctypes]

EngineLib.stateBranch.argtypes = [StateObj]
EngineLib.stateBranch.restype=ctypes.py_object
EngineLib.init_Ijk_call_back.argtypes=[ijk_callback_ctypes]
EngineLib.hook_pass_code.argtypes=[StateObj, ctypes.c_int64];
EngineLib.mem_map.argtypes=[StateObj, ctypes.c_uint64, ctypes.c_uint64]
EngineLib.mem_map.restype=ctypes.c_uint64
EngineLib.mem_unmap.argtypes=[StateObj, ctypes.c_uint64, ctypes.c_uint64]
EngineLib.mem_unmap.restype=ctypes.c_uint64
