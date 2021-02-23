#ifndef _IRSB_CACHE_HEAD_
#define _IRSB_CACHE_HEAD_

#include "engine/engine.h"
#include <deque>
#include "engine/ref.h"

class IRSBCache;
namespace TR {
    class MBase;
};
class IRSB_CHUNK : public ref_manager {
    std::atomic_int32_t m_used_count = 0;
    IRSB* m_irsb;
    ULong m_checksum;
    Addr  m_bb_base;
    ULong m_bb_size; //base block
    std::deque<void*> m_transfer;

public:
    IRSB_CHUNK(IRSB* sb, ULong checksum, Addr bbb, ULong bbs, std::deque<void*>& transfer)
        :m_irsb(sb),
        m_checksum(checksum),
        m_bb_base(bbb),
        m_bb_size(bbs),
        m_transfer(transfer)
    {
        //if (!m_last_chunk.empty()) {
        //    auto it = m_last_chunk.begin();
        //    for (; it != m_last_chunk.end();) {
        //        delete *it;
        //    }
        //    m_last_chunk.clear();
        //}
    };
    auto get_bb_base() const { return m_bb_base; }
    auto get_bb_size() const { return m_bb_size; }
    auto get_checksum()const { return m_checksum; }
    auto get_irsb() {
        m_used_count++;
        return m_irsb;
    }
    auto get_transfer() const { return m_transfer; }


    void clean_call() {
        for (auto alloc_tmp : m_transfer) {
            free(alloc_tmp);
        }
    }

    virtual ~IRSB_CHUNK() {
        clean_call();
    }

    virtual void self_del() { delete this; }
};


IRSBCache* new_IRSBCache();
void del_IRSBCache(IRSBCache* c);
ref<IRSB_CHUNK> irsb_cache_find(IRSBCache* c, TR::MBase& mem, HWord ea);
ref<IRSB_CHUNK> irsb_cache_push(IRSBCache* c, TR::MBase& mem, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc);

IRSBCache* host_get_IRSBCache();
void host_clean_IRSBCache(IRSBCache* c);
ref<IRSB_CHUNK> host_irsb_cache_find(IRSBCache* c, HWord ea);
ref<IRSB_CHUNK> host_irsb_cache_push(IRSBCache* c, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc);
ref<IRSB_CHUNK> ado_treebuild(IRSBCache* c, VexArch arch_guest, ref<IRSB_CHUNK> src, VexRegisterUpdates pxControl);
void irsb_cache_push(IRSBCache* c, ref<IRSB_CHUNK> inbb);


#endif // !_IRSB_CACHE_HEAD_
