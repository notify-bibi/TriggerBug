import re
from .Ijk_NoDecode import *
from .Ijk_SigSEGV import *
from .Ijk_Sys_syscall import *
_regex = re.compile("'(Ijk_\w+)': <function ")
_IjkFuns = {}
for fun in _regex.findall(str(globals())):
    _IjkFuns[fun] = globals()[fun]
