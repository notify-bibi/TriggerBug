import logging
import re
import os
_log = logging.getLogger(name=__name__)
import builtins

def get_IjkFuns():
    import archinfo
    from TriggerBug.TriggerBug import Guest_Arch,GuestArchSystem

    if isinstance(Guest_Arch,archinfo.ArchAMD64) and GuestArchSystem=='linux':
        m = __import__("Linux_AMD64", globals(), locals(), [], 1)
        return m._IjkFuns
        # print(id(m.__builtins__), k)
    if isinstance(Guest_Arch,archinfo.ArchX86) and GuestArchSystem=='windows':
        m = __import__("Win_X86", globals(), locals(), [], 1)
        return m._IjkFuns
    else:
        _log.error(r"U need add system %s arch: %s model at Engine\Ijk_call(like \Linux_AMD64)", GuestArchSystem, Guest_Arch)