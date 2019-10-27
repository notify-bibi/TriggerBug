from TriggerBug.TriggerBugConst import *
import capstone
import logging
log = logging.getLogger(name=__name__)
unsupport=['xrstor']

def Ijk_SigSEGV(*args):
	state=args[0]
	insn=state.Disasm(1)[0]
	if( insn.mnemonic not in unsupport):
		log.error("\tIjk_SigSEGV: \t0x%x:\t: %s\t%s" % (insn.address, insn.mnemonic, insn.op_str))
		return Death
	else:
		log.error("\tIjk_SigSEGV: \t0x%x:\tpass this code : %s\t%s" % (insn.address, insn.mnemonic, insn.op_str))
		state.hook_pass_code(insn.size)
		return Running