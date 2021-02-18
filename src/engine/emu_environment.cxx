#include "engine/emu_environment.h"
#include "engine/register.h"
#include "engine/state_base.h"
#include "engine/memory.h"
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

    sv::tval& IR_Manager::operator[](UInt idx)
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
        void push(IRSB* irsb, std::deque<void*>&& irsb_mem_alloc) {

        }

        IRSB* find(HWord guest_addr) {
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

    static IRSBCache irsbCache;

    // ------------------------EmuEnvGuest--------------------------

    static const UChar* guest_insn_control_method_imp(void* instance, Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code) {
        Mem* mem = (Mem*)instance;
        return mem->libvex_guest_insn_control(guest_IP_sbstart, delta, guest_code);
    };

    EmuEnvGuest::EmuEnvGuest(vex_info const& info, MBase& mem_obj)
        : EmuEnvironment(info.gguest(), info.gtraceflags()),
          m_info(const_cast<vex_info&>(info)), 
          m_ir_temp(mem_obj.ctx()),
          m_mem(mem_obj)
    {
    }

    void EmuEnvGuest::set_guest_bb_insn_control_obj()
    {
        //set guest code bytes unlinear addr
        bb_insn_control_obj_set((void*)&m_mem, guest_insn_control_method_imp);
    }


    void EmuEnvGuest::malloc_ir_buff(Z3_context ctx)
    {
        set_guest_bb_insn_control_obj();
    }

    void EmuEnvGuest::free_ir_buff()
    {
    }

    IRSB* EmuEnvGuest::translate_front(HWord ea)
    {
        set_guest_bb_insn_control_obj();
        /*if (ea == 0x77736009) {
            printf("xd");
        }*/
        VexRegisterUpdates pxControl;
        VexTranslateResult res;
        IRSB* cache_irsb = irsbCache.find(ea);
        if (LIKELY(cache_irsb != nullptr)) {
            return cache_irsb;
        }

        VexTranslateArgs* vta = get_ir_vex_translate_args();
        set_guest_bytes_addr(m_mem.get_vex_insn_linear(ea), ea);
        IRSB* irsb = LibVEX_FrontEnd(vta, &res, &pxControl);
        // irsb = dirty_code_deal_BB(irsb);
        // irsbCache.push(irsb, LibVEX_IRSB_transfer());
        return irsb;

        //static ctx64 v(VexArchAMD64, "");
        //IRSB* bb = emu_ev.translate_front(mem, (Addr)func);
        //static TR::EmuEnvironment emu_ev(v, mem, VexArchAMD64);
    }

    sv::tval& EmuEnvGuest::operator[](UInt idx)
    {
        return m_ir_temp[idx];
    }



    void EmuEnvironment::set_start(HWord s)
    {
        m_guest_start_of_block = s;
        m_is_dynamic_block = false;
    }

    void EmuEnvironment::set_guest_bytes_addr(const UChar* bytes, Addr64 virtual_addr)
    {
        m_vta_chunk.guest_bytes = bytes;
        m_vta_chunk.guest_bytes_addr = virtual_addr;
        set_start(virtual_addr);
    }

    void EmuEnvironment::set_host_addr(Addr64 host_virtual_addr)
    {
        m_vta_chunk.guest_bytes = (UChar*)(host_virtual_addr);
        m_vta_chunk.guest_bytes_addr = host_virtual_addr;
    }
    


    void EmuEnvironment::set_vta_chunk(VexArch arch, ULong traceflags)
    {
        vex_info::init_vta_chunk(m_vta_chunk, m_vge_chunk, arch, traceflags);
    }

    IRSB* EmuEnvironment::find(HWord ea)
    {
        return irsbCache.find(ea);;
    }

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
    
};


