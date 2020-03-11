#pragma once
#ifndef _ENV_VEX_
#define _ENV_VEX_

#include "engine/state_class.h"

namespace TR {

    template<unsigned int MAX_TMP>
    class EmuEnvironment {
        UChar  m_ir_temp_trunk[MAX_TMP * sizeof(Vns)];
        Pap    m_pap;
        Addr64 m_guest_start_of_block = 0;
        bool   m_is_dynamic_block = false;//Need to refresh IRSB memory?
        VexTranslateArgs    m_vta_chunk;
        VexGuestExtents     m_vge_chunk;
        vex_info&           m_info;
    public:
        template<typename ADDR>
        static unsigned char* mem_next_page(void* pap) {
            Pap* p = (Pap*)pap;
            MEM<ADDR>* mem_obj = (MEM<ADDR>*)p->mem_obj;
            return mem_obj->get_next_page(p->guest_addr);
        }

        //guest
        EmuEnvironment(vex_info const& info, MEM<Addr64>& mem_obj) :m_info(info) {
            m_pap.mem_obj = (void*)(&mem_obj);
            m_pap.n_page_mem = mem_next_page<Addr64>;
            m_pap.guest_max_insns = info.guest_max_insns;
            vex_info::init_vta_chunk(m_vta_chunk, m_vge_chunk, info.guest, info.traceflags);
            for (int j = 0; j < MAX_TMP; j++) { ((Vns*)m_ir_temp_trunk)[j].Vns::Vns((Z3_context)mem_obj, 0); }
        }
        EmuEnvironment(vex_info const& info, MEM<Addr32>& mem_obj) :m_info(info) {
            m_pap.mem_obj = (void*)(&mem_obj);
            m_pap.n_page_mem = mem_next_page<Addr32>;
            m_pap.guest_max_insns = info.guest_max_insns;
            vex_info::init_vta_chunk(m_vta_chunk, m_vge_chunk, info.guest, info.traceflags);
            for (int j = 0; j < MAX_TMP; j++) { ((Vns*)m_ir_temp_trunk)[j].Vns::Vns((Z3_context)mem_obj, 0); }
        }
        inline void set_start(Addr64 s) { m_guest_start_of_block = s; m_is_dynamic_block = false; }
        inline void set_guest_bytes_addr(UChar* bytes, Addr64 virtual_addr) {
            m_pap.start_swap = 0;
            m_pap.guest_max_insns = m_info.guest_max_insns;
            m_vta_chunk.guest_bytes = bytes;
            m_vta_chunk.guest_bytes_addr = virtual_addr;
            set_start(virtual_addr);
        };
        template<typename ADDR>
        inline void set_guest_code_temp(MEM<ADDR>& mem_obj, Addr64 virtual_addr, Hook_struct const& hs) {
            *(__m128i*)(m_pap.swap) = mem_obj.Iex_Load<Ity_V256>(virtual_addr);
            memcpy(m_pap.swap, &hs.original.m64_u8, hs.nbytes);
            m_pap.start_swap = 2;
            m_pap.guest_max_insns = 1;
            set_guest_bytes_addr((UChar*)(m_pap.swap), (Addr64)virtual_addr);
        }

        //host
        EmuEnvironment(vex_info const& info, Z3_context ctx, VexArch host) :m_info(info) {
            m_pap.mem_obj = nullptr;
            m_pap.n_page_mem = nullptr;
            m_pap.guest_max_insns = 100;
            m_pap.start_swap = 2;
            vex_info::init_vta_chunk(m_vta_chunk, m_vge_chunk, host, info.traceflags);
            for (int j = 0; j < MAX_TMP; j++) { ((Vns*)m_ir_temp_trunk)[j].Vns::Vns(ctx, 0); }
        }
        inline void set_host_addr(Addr64 host_virtual_addr) {
            m_pap.start_swap = 2;
            m_pap.guest_max_insns = 100;
            m_vta_chunk.guest_bytes = (UChar*)(host_virtual_addr);
            m_vta_chunk.guest_bytes_addr = host_virtual_addr;
        }

        inline Vns& operator[](UInt idx) { return reinterpret_cast<Vns*>(&m_ir_temp_trunk)[idx]; }
        inline Pap* operator->() { return &m_pap; }
        inline operator Pap* () { return &m_pap; }
        inline operator Vns* () { return (Vns*)m_ir_temp_trunk; }
        inline operator VexTranslateArgs* () { return &m_vta_chunk; }
        inline operator VexGuestExtents* () { return &m_vge_chunk; }
        inline operator VexTranslateArgs& () { return m_vta_chunk; }
        inline operator VexGuestExtents& () { return m_vge_chunk; }
        inline operator Pap& () { return m_pap; }

        inline void block_integrity(Addr64 address) {
            Addr64 delta = (address)-m_guest_start_of_block;
            if (delta > 0 && delta < m_pap.delta) {
                vex_printf("\n********* code: %p has been patched!! *********\n", (address));
                m_is_dynamic_block = true;
            }
        }
        inline bool check() { return m_is_dynamic_block; };
        ~EmuEnvironment() {
            for (int j = 0; j < MAX_TMP; j++) { ((Vns*)m_ir_temp_trunk)[j].Vns::~Vns(); }
        }
    };


};


#endif  //! _ENV_VEX_;