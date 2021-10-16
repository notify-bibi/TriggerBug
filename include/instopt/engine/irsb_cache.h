#ifndef _IRSB_CACHE_HEAD_
#define _IRSB_CACHE_HEAD_

#include "instopt/engine/engine.h"
#include <deque>


class IRSBCache;
namespace TR {
    class MBase;
};
namespace bb {
    class IRSB_CHUNK {
        std::atomic_int32_t m_used_count = 0;
        IRSB* m_irsb;
        ULong m_checksum;
        Addr  m_bb_base;
        ULong m_bb_size; //base block
        VexArch m_arch;
        std::deque<void*> m_transfer;

    public:
        IRSB_CHUNK(IRSB* sb, VexArch arch,  ULong checksum, Addr bbb, ULong bbs, std::deque<void*>& transfer)
            :m_irsb(sb),
            m_checksum(checksum),
            m_bb_base(bbb),
            m_bb_size(bbs),
            m_arch(arch),
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
        auto get_arch() const { return m_arch; };
        unsigned get_numBits() const;
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
};

using irsb_chunk = std::shared_ptr<bb::IRSB_CHUNK>;

IRSBCache* new_IRSBCache();
void del_IRSBCache(IRSBCache* c);
irsb_chunk irsb_cache_find(IRSBCache* c, TR::MBase& mem, HWord ea);
irsb_chunk irsb_cache_push(IRSBCache* c, TR::MBase& mem, VexArch arch, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc);

IRSBCache* host_get_IRSBCache();
void host_clean_IRSBCache(IRSBCache* c);
irsb_chunk host_irsb_cache_find(IRSBCache* c, HWord ea);
irsb_chunk host_irsb_cache_push(IRSBCache* c, VexArch arch, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc);
irsb_chunk ado_treebuild(IRSBCache* c, irsb_chunk src, VexRegisterUpdates pxControl);
void irsb_cache_push(IRSBCache* c, irsb_chunk inbb);


#endif // !_IRSB_CACHE_HEAD_
