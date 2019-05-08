
import ctypes

class StateObj(ctypes.c_void_p):
  def __init__(self, state):
      self._as_parameter_ = state
  def from_param(obj):
      return obj

