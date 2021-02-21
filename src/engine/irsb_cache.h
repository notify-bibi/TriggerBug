#ifndef _IRSB_CACHE_HEAD_
#define _IRSB_CACHE_HEAD_

#include "engine/engine.h"
#include "engine/memory.h"
#include <deque>

class IRSBCache;
IRSBCache* new_IRSBCache();
void del_IRSBCache(IRSBCache* c);
IRSB* irsb_cache_find(IRSBCache* c, TR::MBase& mem, HWord ea);
void irsb_cache_push(IRSBCache* c, TR::MBase& mem, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc);

IRSBCache* host_get_IRSBCache();
void host_clean_IRSBCache(IRSBCache* c);
IRSB* host_irsb_cache_find(IRSBCache* c, HWord ea);
void host_irsb_cache_push(IRSBCache* c, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc);




#endif // !_IRSB_CACHE_HEAD_
