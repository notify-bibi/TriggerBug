from TriggerBug.TriggerBugConst import *
import capstone
import logging
log = logging.getLogger(name=__name__)


def Ijk_NoDecode(*args):
	state=args[0]
	insns, bytes = state.Disasm(1)
	insn=insns[0]
	if insn.mnemonic in 'xsavec':
		state.mem_w(insn.address+1,0xAE,1)
	else:
		log.error("\tIjk_NoDecode: \t0x%x:\tpass this code : %s\t%s" %(insn.address, insn.mnemonic, insn.op_str))
		state.hook_pass_code(insn.size)
	return Running