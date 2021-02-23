
#include "engine/irsb_cache.h"
#include "engine/memory.h"
#include <list>
#include <cstddef>
#include <stdexcept>
#include "engine/ref.h"
extern "C" {
    #include "guest_x86_defs.h"
    #include "guest_amd64_defs.h"
    #include "guest_arm_defs.h"
    #include "guest_arm64_defs.h"
    #include "guest_ppc_defs.h"
    #include "guest_mips_defs.h"
    #include "guest_nanomips_defs.h"
    #include <ir_opt.h>
};

#define GUEST_CACHE_CAPACITY 200
#define HOST_CACHE_CAPACITY 50
#define CACHE_PP_RATIO
//#define CACHE_PP

std::deque<void*> LibVEX_IRSB_transfer(void);

namespace cache {

    template<typename key_t, typename value_t>
    class lru_cache {
    public:
        typedef typename std::pair<key_t, value_t> key_value_pair_t;
        typedef typename std::list<key_value_pair_t>::iterator list_iterator_t;

        lru_cache(size_t max_size) :
            _max_size(max_size) {
        }

        void put(const key_t& key, const value_t& value) {
            auto it = _cache_items_map.find(key);
            _cache_items_list.push_front(key_value_pair_t(key, value));
            if (it != _cache_items_map.end()) {
                _cache_items_list.erase(it->second);
                _cache_items_map.erase(it);
            }
            _cache_items_map[key] = _cache_items_list.begin();

            if (_cache_items_map.size() > _max_size) {
                auto last = _cache_items_list.end();
                last--;
                _cache_items_map.erase(last->first);
                _cache_items_list.pop_back();
            }
        }

        const value_t& get(const key_t& key) {
            auto it = _cache_items_map.find(key);
            if (it == _cache_items_map.end()) {
                throw std::range_error("There is no such key in cache");
            }
            else {
                _cache_items_list.splice(_cache_items_list.begin(), _cache_items_list, it->second);
                return it->second->second;
            }
        }

        bool exists(const key_t& key) const {
            return _cache_items_map.find(key) != _cache_items_map.end();
        }

        size_t size() const {
            return _cache_items_map.size();
        }

    private:
        std::list<key_value_pair_t> _cache_items_list;
        std::unordered_map<key_t, list_iterator_t> _cache_items_map;
        size_t _max_size;
    };

} 

// namespace cache

class IRSBCache {
public:
    using _Kty = HWord; // ea
    using REF_IRSB_CHUNK = ref<IRSB_CHUNK>;   // IRSB_CHUNK *

    using CacheType = cache::lru_cache<_Kty, REF_IRSB_CHUNK>;
private:
    CacheType m_cache;

    std::atomic_int32_t m_miss = 0;
    std::atomic_int32_t m_hit = 0;
    Addr m_last_cache_ea;
    const char* m_say;
public:
    IRSBCache(UInt sz, const char* saysome) : m_cache(sz), m_say(saysome) {

    }
    REF_IRSB_CHUNK push(IRSB* irsb, Addr ea, UInt sz, HWord checksum, std::deque<void*>& irsb_mem_alloc) {
        IRSB_CHUNK* ic = new IRSB_CHUNK(irsb, checksum, ea, sz, irsb_mem_alloc);
        push(ic);
        return ic;
    }

    void push(REF_IRSB_CHUNK bb) {
        if (m_cache.exists(bb->get_bb_base())) {
            const REF_IRSB_CHUNK& old = m_cache.get(bb->get_bb_base()); // j��������Ϊ ic
        }
        m_cache.put(bb->get_bb_base(), bb);
    }

    REF_IRSB_CHUNK ado_treebuild(VexArch arch_guest, REF_IRSB_CHUNK src, VexRegisterUpdates pxControl) {
        
        //ppIRSB(irsb);
        Bool(*preciseMemExnsFn) (Int, Int, VexRegisterUpdates);

        switch (arch_guest) {
        case VexArchX86:
            preciseMemExnsFn = guest_x86_state_requires_precise_mem_exns;
            break;
        case VexArchAMD64:
            preciseMemExnsFn = guest_amd64_state_requires_precise_mem_exns;
            break;
        default:
            vpanic("LibVEX_Codegen: unsupported guest insn set");
        }
        Addr max_ga = ado_treebuild_BB(src->get_irsb(), preciseMemExnsFn, pxControl);
        auto junk = LibVEX_IRSB_transfer();
        
            // -----------
            IRSB* dst;
            dst = emptyIRSB();
            dst->tyenv = deepCopyIRTypeEnv(src->get_irsb()->tyenv);
            dst->offsIP = src->get_irsb()->offsIP;
            concatenate_irsbs(dst, src->get_irsb());
            auto irsb_mem_alloc = LibVEX_IRSB_transfer();
            // ------------

        for (auto alloc_tmp : junk) {
            free(alloc_tmp);
        }

        IRSB_CHUNK* ic = new IRSB_CHUNK(dst, src->get_checksum(), src->get_bb_base(), src->get_bb_size(), irsb_mem_alloc);
        vassert(max_ga == src->get_bb_base() + src->get_bb_size() - 1);
        return ic;
    }

    REF_IRSB_CHUNK find(TR::MBase& mem, HWord ea) {

        if UNLIKELY(!m_cache.exists(ea)) {
#ifdef CACHE_PP
            printf("Cache miss %p\n", ea);
#endif
            m_miss++;
            return nullptr;
        }
        else if (m_last_cache_ea != ea) {
            m_hit++;
            m_last_cache_ea = ea;
#ifdef CACHE_PP
            printf("Cache Hit %p\n", ea);
#endif
        }
        auto ic = m_cache.get(ea);
        HWord checksum = mem.genericg_compute_checksum(ic->get_bb_base(), ic->get_bb_size());
        if LIKELY(ic->get_checksum() == checksum) {
            return ic;
        }
        std::cout << "irsb cache updated" << std::endl;
        return nullptr;
    }


    bool destoryIRSB(IRSB* irsb) {

    }

    bool refresh() {

    }

    void clean_all() {

    }
    void clean() {

    }

    ref<IRSB_CHUNK> host_find(HWord hea) {
        if UNLIKELY(!m_cache.exists(hea)) return nullptr;
        auto ic = m_cache.get(hea);
        return ic;
    }

    ~IRSBCache() {
#if defined( CACHE_PP ) || defined(CACHE_PP_RATIO)
        printf("%s\n", m_say);
        printf("TR Tanslate Cache Size : %d\n", m_cache.size());
        printf("TR Tanslate Cache Access Count : %d\n", m_miss + m_hit);
        printf("TR Tanslate Cache Hit Rate : %f%%\n", (float)m_hit / (float)(m_miss + m_hit) * 100);
#endif
        clean_all();
    }
};


IRSBCache* new_IRSBCache() { return new IRSBCache(GUEST_CACHE_CAPACITY, "-------- Guest LRU Cache -----------"); }

void del_IRSBCache(IRSBCache* c) { 
    delete c; 
}

ref<IRSB_CHUNK> irsb_cache_find(IRSBCache* c, TR::MBase& mem, HWord ea) {
    return c->find(mem, ea);
}

ref<IRSB_CHUNK> irsb_cache_push(IRSBCache* c, TR::MBase& mem, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc) {
    Addr     base2check;
    UInt     len2check;
    HWord    expectedhW;

    //for (Int i = 0; i < vge->n_used; i++) {
        base2check = vge->base[0];
        len2check = vge->len[0];
        //if (len2check == 0)
   //         continue;
        expectedhW = mem.genericg_compute_checksum(base2check, len2check);
        return c->push(irsb, base2check, len2check, expectedhW, irsb_mem_alloc);
   // }

}



// ������Ҫ����
IRSBCache* host_get_IRSBCache() {
    static IRSBCache host_cache(HOST_CACHE_CAPACITY, "-------- Host LRU Cache -----------");
    return &host_cache;

}
void host_clean_IRSBCache(IRSBCache* c) {
    c->clean();
}

ref<IRSB_CHUNK> host_irsb_cache_find(IRSBCache* c, HWord ea) {
    return c->host_find(ea);
}
ref<IRSB_CHUNK> host_irsb_cache_push(IRSBCache* c, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc) {
    Addr     base2check;
    UInt     len2check;
    base2check = vge->base[0];
    len2check = vge->len[0];
    return c->push(irsb, base2check, len2check, 0x2333, irsb_mem_alloc);
}


ref<IRSB_CHUNK> ado_treebuild(IRSBCache* c, VexArch arch_guest, ref<IRSB_CHUNK> src, VexRegisterUpdates pxControl) {
    return c->ado_treebuild(arch_guest, src, pxControl);
}


void irsb_cache_push(IRSBCache* c, ref<IRSB_CHUNK> inbb) {
    c->push(inbb);
}