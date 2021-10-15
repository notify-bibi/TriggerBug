
#include "instopt/engine/irsb_cache.h"
#include "instopt/engine/memory.h"
#include <list>
#include <cstddef>
#include <stdexcept>

extern "C" {
    #include "../valgrind-3.17.0/VEX/priv/guest_x86_defs.h"
    #include "../valgrind-3.17.0/VEX/priv/guest_amd64_defs.h"
    #include "../valgrind-3.17.0/VEX/priv/guest_arm_defs.h"
    #include "../valgrind-3.17.0/VEX/priv/guest_arm64_defs.h"
    #include "../valgrind-3.17.0/VEX/priv/guest_ppc_defs.h"
    #include "../valgrind-3.17.0/VEX/priv/guest_mips_defs.h"
    #include "../valgrind-3.17.0/VEX/priv/guest_nanomips_defs.h"
    #include "../valgrind-3.17.0/VEX/priv/ir_opt.h"
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
    using CacheType = cache::lru_cache<_Kty, irsb_chunk>;
private:
    CacheType m_cache;

    std::atomic_int32_t m_miss = 0;
    std::atomic_int32_t m_hit = 0;
    Addr m_last_cache_ea;
    const char* m_say;

    spin_mutex m_lock;
public:
    IRSBCache(UInt sz, const char* saysome) : m_cache(sz), m_say(saysome) {

    }
    auto push(IRSB* irsb, VexArch arch, Addr ea, UInt sz, HWord checksum, std::deque<void*>& irsb_mem_alloc) {
        auto ic = std::make_shared<bb::IRSB_CHUNK>(irsb, arch, checksum, ea, sz, irsb_mem_alloc);
        push(ic);
        return ic;
    }

    void push(irsb_chunk bb) {
        spin_unique_lock lock(m_lock);
        if (m_cache.exists(bb->get_bb_base())) {
            irsb_chunk old = m_cache.get(bb->get_bb_base()); // j即将更新为 ic
        }
        m_cache.put(bb->get_bb_base(), bb);
    }

    irsb_chunk ado_treebuild(irsb_chunk src, VexRegisterUpdates pxControl) {

        IRSB* src_irsb = deepCopyIRSB(src->get_irsb());

        //ppIRSB(irsb);
        Bool(*preciseMemExnsFn) (Int, Int, VexRegisterUpdates);
        
        switch (src->get_arch()) {
        case VexArchX86:
            preciseMemExnsFn = guest_x86_state_requires_precise_mem_exns;
            break;
        case VexArchAMD64:
            preciseMemExnsFn = guest_amd64_state_requires_precise_mem_exns;
            break;
        default:
            VPANIC("LibVEX_Codegen: unsupported guest insn set");
        }
        Addr max_ga = ado_treebuild_BB(src_irsb, preciseMemExnsFn, pxControl);
        auto junk = LibVEX_IRSB_transfer();
        
            // -----------
            IRSB* dst;
            /*dst = emptyIRSB();
            dst->tyenv = deepCopyIRTypeEnv(src->get_irsb()->tyenv);
            dst->offsIP = src->get_irsb()->offsIP;
            concatenate_irsbs(dst, src->get_irsb());*/
            dst = deepCopyIRSB(src_irsb);

            auto irsb_mem_alloc = LibVEX_IRSB_transfer();
            // ------------

        for (auto alloc_tmp : junk) {
            free(alloc_tmp);
        }

        irsb_chunk ic = std::make_shared<bb::IRSB_CHUNK>(dst, src->get_arch(), src->get_checksum(), src->get_bb_base(), src->get_bb_size(), irsb_mem_alloc);
        if UNLIKELY(max_ga != src->get_bb_base() + src->get_bb_size() - 1) {
            //may be ir  not decode success
            spdlog::error("error size may be ir  not decode success {:x}", max_ga);
        }
        return ic;
    }

    irsb_chunk find(TR::MBase& mem, HWord ea) {
        irsb_chunk ic;
        {
            spin_unique_lock lock(m_lock);
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
            ic = irsb_chunk(m_cache.get(ea));
        };
        HWord checksum = mem.genericg_compute_checksum(ic->get_bb_base(), ic->get_bb_size());
        if LIKELY(ic->get_checksum() == checksum) {
            return ic;
        }
        std::cout << "irsb cache updated" << std::endl;
        return nullptr;
    }


    bool destoryIRSB(IRSB* irsb) {
        return true;
    }

    bool refresh() {
        return true;
    }

    void clean_all() {

    }
    void clean() {

    }

    irsb_chunk host_find(HWord hea) {
        spin_unique_lock lock(m_lock);
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

irsb_chunk irsb_cache_find(IRSBCache* c, TR::MBase& mem, HWord ea) {
    return c->find(mem, ea);
}

irsb_chunk irsb_cache_push(IRSBCache* c, TR::MBase& mem, VexArch arch, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc) {
    Addr     base2check;
    UInt     len2check;
    HWord    expectedhW;

    //for (Int i = 0; i < vge->n_used; i++) {
        base2check = vge->base[0];
        len2check = vge->len[0];
        //if (len2check == 0)
   //         continue;
        expectedhW = mem.genericg_compute_checksum(base2check, len2check);
        return c->push(irsb, arch, base2check, len2check, expectedhW, irsb_mem_alloc);
   // }

}



// 后期需要加锁
IRSBCache* host_get_IRSBCache() {
    static IRSBCache host_cache(HOST_CACHE_CAPACITY, "-------- Host LRU Cache -----------");
    return &host_cache;

}
void host_clean_IRSBCache(IRSBCache* c) {
    c->clean();
}

irsb_chunk host_irsb_cache_find(IRSBCache* c, HWord ea) {
    return c->host_find(ea);
}
irsb_chunk host_irsb_cache_push(IRSBCache* c, VexArch arch, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc) {
    Addr     base2check;
    UInt     len2check;
    base2check = vge->base[0];
    len2check = vge->len[0];
    
    return c->push(irsb, arch, base2check, len2check, 0x2333, irsb_mem_alloc);
}


irsb_chunk ado_treebuild(IRSBCache* c, irsb_chunk src, VexRegisterUpdates pxControl) {
    return c->ado_treebuild(src, pxControl);
}


void irsb_cache_push(IRSBCache* c, irsb_chunk inbb) {
    c->push(inbb);
}