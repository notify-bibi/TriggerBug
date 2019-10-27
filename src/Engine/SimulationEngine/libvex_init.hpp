#pragma once
#ifndef LIBVEX_INIT
#define LIBVEX_INIT

__attribute__((noreturn))
void failure_exit();
void _vex_log_bytes(const HChar* bytes, SizeT nbytes);
void vex_hwcaps_vai(VexArch arch, VexArchInfo* vai);
void vex_prepare_vbi(VexArch arch, VexAbiInfo* vbi);
UInt needs_self_check(void* callback_opaque, VexRegisterUpdates* pxControl, const VexGuestExtents* guest_extents);
void* dispatch(void);
Bool chase_into_ok(void* value, Addr addr);
std::string replace(const char* pszSrc, const char* pszOld, const char* pszNew);
extern void Func_Map_Init();
void IR_init(VexControl& vc);

#endif