#include "engine/emu_environment.h"
#include "engine/register.h"
#include "engine/state_base.h"
#include "engine/memory.h"
#include "gen_global_var_call.hpp"
#include "engine/irsb_cache.h"


IRSB* irsb_cache_find(HWord ea);

#ifdef VEX_BACKEND_FN
void (*libvex_BackEnd)(const VexTranslateArgs * vta,
    /*MOD*/ VexTranslateResult * res,
    /*MOD*/ IRSB * irsb,
    VexRegisterUpdates pxControl);


void set_cvdf(void*p) {
    libvex_BackEnd = (decltype(libvex_BackEnd))p;
}
#endif

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
        if (m_size_ir_temp <= tidx) {
            vassert(m_size_ir_temp == m_ir_unit.size());
            for (UInt idx = m_ir_unit.size(); idx <= tidx; idx++) {
                m_ir_unit.emplace_back(nullptr);
            }
            m_size_ir_temp = tidx + 1;
        }
        if(!m_ir_unit[tidx]) m_ir_unit[tidx] = new tval_thunk(m_ctx);
        return m_ir_unit[tidx]->operator[](idx% MAX_IRTEMP);
    }

    IR_Manager::~IR_Manager()
    {
        for (auto p : m_ir_unit) {
            if(p) delete p;
        }
    }


    // ------------------------EmuEnvGuest--------------------------

    static const UChar* guest_insn_control_method_imp(void* instance, Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code) {
        Mem* mem = (Mem*)instance;
        return mem->libvex_guest_insn_control(guest_IP_sbstart, delta, guest_code);
    };

    EmuEnvGuest::EmuEnvGuest(vex_context& vctx, vex_info const& info, MBase& mem_obj)
        : EmuEnvironment(info.gguest(), info.gtraceflags()),
        m_vctx(vctx),
        m_ir_temp(mem_obj.ctx()),
        m_mem(mem_obj)
    {
    }

    void EmuEnvGuest::block_integrity(Addr wl, UInt sz)
    {
        //std::map<Addr, UInt>::iterator fd = m_cache_map.lower_bound(address);
        //if LIKELY(fd != m_cache_map.end()) {
        //    if UNLIKELY(address <= fd->first + fd->second) {

        //    }
        //}
        Addr wr = wl + sz;
        Addr cr = m_guest_start_of_block + m_base_block_sz;

        if UNLIKELY((m_guest_start_of_block <= wr && wr < cr) || (m_guest_start_of_block <= wl && wl < cr)){
            spdlog::critical("\n********* anti debug [code ea: 0x{:x}] has been patched!! i will updated irsb *********\n", (wl));
            m_is_dynamic_block = true;
        }
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

    irsb_chunk EmuEnvGuest::translate_front(HWord ea)
    {
        set_guest_bb_insn_control_obj();
        /*if (ea == 0x77736009) {
            printf("xd");
        }*/
        
        irsb_chunk cache_irsb = irsb_cache_find(m_vctx.get_irsb_cache(), m_mem, ea);
        if (LIKELY(cache_irsb != nullptr)) {
            return cache_irsb;
        }

        VexTranslateArgs* vta = get_ir_vex_translate_args();
        set_guest_bytes_addr(m_mem.get_vex_insn_linear(ea), ea);
        
        m_guest_start_of_block = ea;
        m_is_dynamic_block = false;
        IRSB* irsb = LibVEX_FrontEnd(vta, &m_res, &m_pxControl);

#ifdef VEX_BACKEND_FN
        if(irsb->jumpkind != Ijk_Sys_int32)
            libvex_BackEnd(vta, get_res(), irsb, *get_pxControl());
        m_base_block_sz = vta->guest_extents->len[0];
#endif
        return irsb_cache_push(m_vctx.get_irsb_cache(), m_mem, vta->guest_extents, irsb, LibVEX_IRSB_transfer());
    }

    sv::tval& EmuEnvGuest::operator[](UInt idx)
    {
        return m_ir_temp[idx];
    }


    void EmuEnvironment::block_integrity(Addr ea, UInt sz) {
        return;
    }


    
    void EmuEnvironment::set_guest_bytes_addr(const UChar* bytes, Addr64 virtual_addr)
    {
        m_vta_chunk.guest_bytes = bytes;
        m_vta_chunk.guest_bytes_addr = virtual_addr;
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


    EmuEnvironment::~EmuEnvironment()
    {
    };
    
};


