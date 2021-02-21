
#include "engine/irsb_cache.h"
#include <list>
#include <cstddef>
#include <stdexcept>
#include "engine/ref.h"

#define GUEST_CACHE_CAPACITY 200
#define HOST_CACHE_CAPACITY 50
#define CACHE_PP_RATIO
//#define CACHE_PP

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

} // namespace cache

class IRSB_CHUNK {
    std::atomic_int32_t m_ref_count = 0;
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

    void inc_ref() {
        m_ref_count++;
    }

    void dec_ref() {
        m_ref_count--;
        vassert(m_ref_count >= 0);
        if (m_ref_count == 0) 
            delete this;
    }

    void clean_call() {
        for (auto alloc_tmp : m_transfer) {
            free(alloc_tmp);
        }
    }

    ~IRSB_CHUNK() {
        vassert(m_ref_count == 0);
        clean_call();
    }
};


//
//class IRSBCache {
//    using _Kty = HWord; // ea
//    using _Vty = IRSB_CHUNK*;   // IRSB_CHUNK *
//    using CacheType = std::unordered_map<_Kty, _Vty>;
//    CacheType m_cache;
//
//
//public:
//    IRSBCache() {
//
//    }
//    void push(IRSB* irsb, Addr ea, UInt sz, HWord checksum, std::deque<void*>& irsb_mem_alloc) {
//        IRSB_CHUNK* ic = new IRSB_CHUNK{ irsb ,checksum, ea, sz , irsb_mem_alloc };
//        CacheType::iterator k = m_cache.find(ea);
//        if (k == m_cache.end()) {
//            m_cache[ea] = ic;
//        }
//        else {
//            for (auto alloc_tmp : k->second->transfer) {
//                free(alloc_tmp);
//            }
//            delete k->second;
//            k->second = ic;
//        }
//         
//    }
//
//    IRSB* find(TR::MBase& mem, HWord guest_addr) {
//        CacheType::iterator k = m_cache.find(guest_addr);
//        if UNLIKELY(k == m_cache.end()) return nullptr;
//        IRSB_CHUNK* ic = k->second;
//        HWord checksum = mem.genericg_compute_checksum(ic->bb_base, ic->bb_size);
//        if LIKELY(ic->checksum == checksum) {
//            return ic->irsb;
//        }
//        std::cout << "irsb cache updated" << std::endl;
//        return nullptr;
//    }
//
//
//    bool destoryIRSB(IRSB* irsb) {
//
//    }
//
//    bool refresh() {
//
//    }
//
//    void clean_all() {
//        if (m_cache.empty()) return;
//        CacheType::iterator it = m_cache.begin();
//        for (; it != m_cache.end(); it = m_cache.erase(it)) {
//            std::deque<void*>& tmp = it->second->transfer;
//            for (auto alloc_tmp : tmp) {
//                free(alloc_tmp);
//            }
//            delete it->second;
//        }
//    }
//    void clean() {
//
//    }
//
//    IRSB* host_find(HWord guest_addr) {
//        CacheType::iterator k = m_cache.find(guest_addr);
//        if UNLIKELY(k == m_cache.end()) return nullptr;
//        IRSB_CHUNK* ic = k->second;
//        return ic->irsb;
//    }
//
//    ~IRSBCache() {
//        clean_all();
//    }
//};


class IRSBCache {
    using _Kty = HWord; // ea
    using _Vty = ref<IRSB_CHUNK>;   // IRSB_CHUNK *

    using CacheType = cache::lru_cache<_Kty, _Vty>;
    CacheType m_cache;

    std::atomic_int32_t m_miss = 0;
    std::atomic_int32_t m_hit = 0;
    Addr m_last_cache_ea;
    const char* m_say;
public:
    IRSBCache(UInt sz, const char* saysome): m_cache(sz), m_say(saysome){

    }
    void push(IRSB* irsb, Addr ea, UInt sz, HWord checksum, std::deque<void*>& irsb_mem_alloc) {
        IRSB_CHUNK* ic = new IRSB_CHUNK( irsb , checksum, ea, sz , irsb_mem_alloc );
        if (!m_cache.exists(ea)) {
            m_cache.put(ea, ic);
        }
        else {
            delete ic;
        }

    }

    IRSB* find(TR::MBase& mem, HWord ea) {

        if UNLIKELY(!m_cache.exists(ea)) {
#ifdef CACHE_PP
            printf("Cache miss %p\n", ea);
#endif
            m_miss++;
            return nullptr; 
        }
        else if (m_last_cache_ea != ea){
            m_hit++;
            m_last_cache_ea = ea;
#ifdef CACHE_PP
            printf("Cache Hit %p\n", ea);
#endif
        }
        auto ic = m_cache.get(ea);
        HWord checksum = mem.genericg_compute_checksum(ic->get_bb_base(), ic->get_bb_size());
        if LIKELY(ic->get_checksum() == checksum) {
            return ic->get_irsb();
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

    IRSB* host_find(HWord hea) {
        if UNLIKELY(!m_cache.exists(hea)) return nullptr;
        auto ic = m_cache.get(hea);
        return ic->get_irsb();
    }

    ~IRSBCache() {
#if defined( CACHE_PP ) || defined(CACHE_PP_RATIO)
        printf("%s\n", m_say);
        printf("TR Tanslate Cache Size : %d\n", m_cache.size());
        printf("TR Tanslate Cache Access Count : %d\n", m_miss + m_hit);
        printf("TR Tanslate Cache Hit Rate : %f%%\n", (float)m_hit / (float)(m_miss + m_hit)*100);
#endif
        clean_all();
    }
};

IRSBCache* new_IRSBCache() { return new IRSBCache(GUEST_CACHE_CAPACITY, "-------- Guest LRU Cache -----------"); }

void del_IRSBCache(IRSBCache* c) { 
    delete c; 
}

IRSB* irsb_cache_find(IRSBCache* c, TR::MBase& mem, HWord ea) {
    return c->find(mem, ea);
}

void irsb_cache_push(IRSBCache* c, TR::MBase& mem, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc) {
    Addr     base2check;
    UInt     len2check;
    HWord    expectedhW;

    //for (Int i = 0; i < vge->n_used; i++) {
        base2check = vge->base[0];
        len2check = vge->len[0];
        //if (len2check == 0)
   //         continue;
        expectedhW = mem.genericg_compute_checksum(base2check, len2check);
        c->push(irsb, base2check, len2check, expectedhW, irsb_mem_alloc);
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

IRSB* host_irsb_cache_find(IRSBCache* c, HWord ea) {
    return c->host_find(ea);
}
void host_irsb_cache_push(IRSBCache* c, const VexGuestExtents* vge, IRSB* irsb, std::deque<void*>&& irsb_mem_alloc) {
    Addr     base2check;
    UInt     len2check;
    base2check = vge->base[0];
    len2check = vge->len[0];
    c->push(irsb, base2check, len2check, 0x2333, irsb_mem_alloc);
}
