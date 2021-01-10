#include "engine/emu_environment.h"
#include "engine/register.h"
#include "engine/memory.h"
#include "engine/kernel.h"
#include "engine/compress.h"
#include "gen_global_var_call.hpp"

namespace TR {


    void IR_Manager::clear()
    {

    }

    IR_Manager::IR_Manager(Z3_context ctx) :m_ctx(ctx), m_size_ir_temp(0)
    {
        for (std::size_t pos = 0; pos < m_ir_unit.size();++pos) {
            tval_thunk* p = m_ir_unit[pos];
            if (p)  delete p;
            m_ir_unit[pos] = nullptr;
        }
    }

    tval& IR_Manager::operator[](UInt idx) 
    {
        UInt tidx = idx / MAX_IRTEMP;
        if (m_size_ir_temp <= tidx || !m_ir_unit[tidx]) {
            vassert(m_size_ir_temp == m_ir_unit.size());
            for (UInt idx = m_ir_unit.size(); idx <= tidx; idx++) {
                m_ir_unit.emplace_back(nullptr);
            }
            m_ir_unit[tidx] = new tval_thunk(m_ctx);
            m_size_ir_temp = tidx + 1;
        }
        return m_ir_unit[tidx]->operator[](idx% MAX_IRTEMP);
    }

    IR_Manager::~IR_Manager()
    {
        for (auto p : m_ir_unit) {
            if(p) delete p;
        }
    }

    typedef struct IRSB_CHUNK {
        IRSB* irsb;
        ULong hash;
        Addr guest_start, guest_end;
        ULong bbsize; //base block
        bool has_changed; // irsb was old need refresh
    } IRSB_CHUNK;

    class IRSBCache {
        using _Kty = Addr;
        using _Vty = int;
        using CacheType = std::unordered_map<_Kty, _Vty>;
        CacheType m_cache;


    public:
        IRSBCache() {

        }
        void push(IRSB* irsb, std::deque<void*> && irsb_mem_alloc) {
            
        }

        template<typename THword>
        IRSB* find(MEM<THword>& mem, Addr guest_addr) {
            CacheType::iterator k = m_cache.find(guest_addr);
            //mem.mem_real_hash(guest_addr, 0x20);
            // make hash 
            //k->second

            //look up hash



            return nullptr;
        }

        bool destoryIRSB(IRSB* irsb) {

        }

        bool refresh() {
        
        }

        ~IRSBCache() {

        }
    };



    IRSBCache irsbCache;




    template<typename THword>
    EmuEnvironment::EmuEnvironment(vex_info const& info, MEM<THword>& mem_obj, VexArch host)
        : m_info(const_cast<vex_info&>(info)), m_ir_temp(mem_obj.ctx()) {
        vassert((((size_t)this) & 0xf) == 0);
        vex_info::init_vta_chunk(m_vta_chunk, m_vge_chunk, host, info.gtraceflags());
        //set guest code bytes unlinear addr
        bb_insn_control_obj_set((void*)&mem_obj, guest_insn_control_method_imp<THword>);
    }


    void EmuEnvironment::malloc_ir_buff(Z3_context ctx)
    {
        
    }

    void EmuEnvironment::free_ir_buff()
    {
        m_ir_temp.clear();
    }

    template<typename THword>
    IRSB* EmuEnvironment::translate_front(MEM<THword>& mem, Addr guest_addr)
    {
        VexRegisterUpdates pxControl;
        VexTranslateResult res;
        IRSB* cache_irsb = irsbCache.find(mem, guest_addr);
        if (LIKELY(cache_irsb != nullptr)) {
            return cache_irsb;
        }

        VexTranslateArgs* vta = get_ir_vex_translate_args();
        const UChar* bytes_insn = mem.get_vex_insn_linear(guest_addr);
        set_guest_bytes_addr(bytes_insn, guest_addr);
        IRSB* irsb = LibVEX_FrontEnd(vta, &res, &pxControl);
        //irsb = dirty_code_deal_BB(irsb);

        //irsbCache.push(irsb, LibVEX_IRSB_transfer());
        return irsb;
    }

    void EmuEnvironment::set_start(Addr64 s)
    {
        m_guest_start_of_block = s; m_is_dynamic_block = false;
    }

    void EmuEnvironment::set_guest_bytes_addr(const UChar* bytes, Addr64 virtual_addr)
    {
        m_vta_chunk.guest_bytes = bytes;
        m_vta_chunk.guest_bytes_addr = virtual_addr;
        set_start(virtual_addr);
    }
    

//    template<typename THword>
//    void EmuEnvironment::set_guest_code_temp(MEM<THword>& mem_obj, Addr64 virtual_addr, Hook_struct const& hs)
//    {
//        //*(__m128i*)(m_pap.swap) = mem_obj.load<Ity_V256>(virtual_addr).tor();
//        //memcpy(m_pap.swap, &hs.original.m64_u8, hs.nbytes);
//#warning "need check"
//        //m_pap.start_swap = 2;
//        //m_pap.guest_max_insns = 1;
//        //m_vta_chunk.guest_bytes = (UChar*)(m_pap.swap);
//        m_vta_chunk.guest_bytes_addr = virtual_addr;
//    }



    void EmuEnvironment::block_integrity(bool is_code_page, Addr address, UInt insn_block_delta) {
        if (!is_code_page) return;

        std::map<Addr, UInt>::iterator fd = m_cache_map.lower_bound(address);
        if LIKELY(fd != m_cache_map.end()) {
            if UNLIKELY(address <= fd->first + fd->second) {

            }
        }
        Addr delta = (address)-m_guest_start_of_block;
        if (delta > 0 && delta < insn_block_delta) {
            vex_printf("\n********* code: %p has been patched!! *********\n", (address));
            m_is_dynamic_block = true;
        }
    }

    EmuEnvironment::~EmuEnvironment()
    {
    };
    
    template <typename THword>
    static const UChar* guest_insn_control_method_imp(void* instance, Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code) {
        MEM<THword>* mem = (MEM<THword>*)instance;
        return mem->libvex_guest_insn_control(guest_IP_sbstart, delta, guest_code);
    };

    template EmuEnvironment::EmuEnvironment(vex_info const& info, MEM<Addr32>& mem_obj, VexArch host);
    template EmuEnvironment::EmuEnvironment(vex_info const& info, MEM<Addr64>& mem_obj, VexArch host);
    template IRSB* EmuEnvironment::translate_front(MEM<Addr32>& mem, Addr guest_addr);
    template IRSB* EmuEnvironment::translate_front(MEM<Addr64>& mem, Addr guest_addr);
};


