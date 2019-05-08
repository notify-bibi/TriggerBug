VexArch={
'VexArch_INVALID':0x400,
'VexArchX86':0x400+1,
'VexArchAMD64':0x400+2,
'VexArchARM':0x400+3,
'VexArchARM64':0x400+4,
'VexArchPPC32':0x400+5,
'VexArchPPC64':0x400+6,
'VexArchS390X':0x400+7,
'VexArchMIPS32':0x400+8,
'VexArchMIPS64':0x400+9
}

NewState = 0
Running = 1
Fork = 2
Death = 3
State_Tag={NewState:'NewState',Running:'Running',Fork:'Fork',Death:'Death'}

_IRJumpKind =["Ijk_INVALID", "Ijk_Boring", "Ijk_Call", "Ijk_Ret", "Ijk_ClientReq", "Ijk_Yield", "Ijk_EmWarn", "Ijk_EmFail", "Ijk_NoDecode", "Ijk_MapFail", "Ijk_InvalICache", "Ijk_FlushDCache", "Ijk_NoRedir", "Ijk_SigILL", "Ijk_SigTRAP", "Ijk_SigSEGV", "Ijk_SigBUS", "Ijk_SigFPE", "Ijk_SigFPE_IntDiv", "Ijk_SigFPE_IntOvf", "Ijk_Sys_syscall", "Ijk_Sys_int32", "Ijk_Sys_int128", "Ijk_Sys_int129", "Ijk_Sys_int130", "Ijk_Sys_int145", "Ijk_Sys_int210", "Ijk_Sys_sysenter"]

IRJumpKindNmae={}
for index,ijkname in enumerate(_IRJumpKind):
    IRJumpKindNmae[0x1A00+index]=ijkname

del _IRJumpKind