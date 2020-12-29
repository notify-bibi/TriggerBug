#ifndef GEN_GLOAL_VAR_CALL_DEF
#define GEN_GLOAL_VAR_CALL_DEF
extern "C" {
#include "libvex.h"
}
#include <deque>

std::deque<void*> LibVEX_IRSB_transfer(void);
extern void bb_insn_control_obj_set(void* instance, const UChar* (*guest_insn_control_method)(void*, Addr, Long, const UChar*));
extern const UChar* /*out guest_code*/ guest_generic_bb_insn_control(Addr guest_IP_sbstart, Long delta,  /*in guest_code*/ const UChar* guest_code);

#endif