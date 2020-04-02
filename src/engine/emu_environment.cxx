#include "engine/emu_environment.h"

namespace TR {

    template<unsigned int MAX_TMP>
    EmuEnvironment<MAX_TMP>::EmuEnvironment(vex_info const& info, MEM<Addr64>& mem_obj)
        :m_info(info) {
        m_pap.mem_obj = (void*)(&mem_obj);
        m_pap.n_page_mem = mem_next_page<Addr64>;
        m_pap.guest_max_insns = info.gmax_insns();
        vex_info::init_vta_chunk(m_vta_chunk, m_vge_chunk, info.gguest(), info.gtraceflags());
        for (unsigned j = 0; j < MAX_TMP; j++) { ((tval*)m_ir_temp_trunk)[j].tval::tval((Z3_context)mem_obj, 0); }
    }

    template<unsigned int MAX_TMP>
    EmuEnvironment<MAX_TMP>::EmuEnvironment(vex_info const& info, MEM<Addr32>& mem_obj)
        :m_info(info) 
    {
        m_pap.mem_obj = (void*)(&mem_obj);
        m_pap.n_page_mem = mem_next_page<Addr32>;
        m_pap.guest_max_insns = info.gmax_insns();
        vex_info::init_vta_chunk(m_vta_chunk, m_vge_chunk, info.gguest(), info.gtraceflags());
        for (unsigned j = 0; j < MAX_TMP; j++) { ((tval*)m_ir_temp_trunk)[j].tval::tval((Z3_context)mem_obj, 0); }
    }

    template<unsigned int MAX_TMP>
    EmuEnvironment<MAX_TMP>::EmuEnvironment(vex_info const& info, Z3_context ctx, VexArch host):
        m_info(info) 
    {
        m_pap.mem_obj = nullptr;
        m_pap.n_page_mem = nullptr;
        m_pap.guest_max_insns = 100;
        m_pap.start_swap = 2;
        vex_info::init_vta_chunk(m_vta_chunk, m_vge_chunk, host, info.gtraceflags());
        for (unsigned j = 0; j < MAX_TMP; j++) { ((tval*)m_ir_temp_trunk)[j].tval::tval(ctx, 0); }
    }
    


    template<unsigned int MAX_TMP>
    template<typename ADDR>
    void EmuEnvironment<MAX_TMP>::set_guest_code_temp(MEM<ADDR>& mem_obj, Addr64 virtual_addr, Hook_struct const& hs)
    {
        *(__m128i*)(m_pap.swap) = mem_obj.load<Ity_V256>(virtual_addr);
        memcpy(m_pap.swap, &hs.original.m64_u8, hs.nbytes);
        m_pap.start_swap = 2;
        m_pap.guest_max_insns = 1;
        m_vta_chunk.guest_bytes = (UChar*)(m_pap.swap);
        m_vta_chunk.guest_bytes_addr = virtual_addr;
    }


    template<unsigned int MAX_TMP>
    EmuEnvironment<MAX_TMP>::~EmuEnvironment()
    {
        for (int j = 0; j < MAX_TMP; j++) {
            ((tval*)m_ir_temp_trunk)[j].tval::~tval();
        }
    }

};


template TR::EmuEnvironment<800>;
template void TR::EmuEnvironment<800>::set_guest_code_temp(TR::MEM<Addr32>& mem_obj, Addr64 virtual_addr, TR::Hook_struct const& hs);
template void TR::EmuEnvironment<800>::set_guest_code_temp(TR::MEM<Addr64>& mem_obj, Addr64 virtual_addr, TR::Hook_struct const& hs);