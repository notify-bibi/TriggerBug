#pragma once
#ifndef _ENV_VEX_
#define _ENV_VEX_

#include "engine/engine.h"
#include "engine/vex_context.h"

namespace TR {

    template<unsigned int MAX_TMP>
    __declspec(align(32))
    class EmuEnvironment {
        Addr64 m_guest_start_of_block = 0;
        bool   m_is_dynamic_block = false;//Need to refresh IRSB memory?
        VexTranslateArgs    m_vta_chunk;
        VexGuestExtents     m_vge_chunk;
        vex_info&           m_info;
        UChar*              m_ir_temp_trunk;
    public:
        //init vex
        template<typename THword>
        EmuEnvironment(vex_info const& info, MEM<THword>& mem_obj, VexArch host);
        /*
        template<>
        EmuEnvironment(vex_info const& info, MEM<Addr32>& mem_obj, VexArch host);
        template<>
        EmuEnvironment(vex_info const& info, MEM<Addr64>& mem_obj, VexArch host);*/

        //new ir temp
        void malloc_ir_buff(Z3_context ctx);
        //free ir temp
        void free_ir_buff();
        // translate
        template<typename THword>
        IRSB* translate_front(MEM<THword>& mem, Addr guest_addr);
        //set guest_start_of_block to check block changed by guest
        inline void set_start(Addr64 s) { m_guest_start_of_block = s; m_is_dynamic_block = false; }

        void set_guest_bytes_addr(const UChar* bytes, Addr64 virtual_addr);

        template<typename THword>
        void set_guest_code_temp(MEM<THword>& mem_obj, Addr64 virtual_addr, Hook_struct const& hs);

        

        inline void set_host_addr(Addr64 host_virtual_addr) {
            m_vta_chunk.guest_bytes = (UChar*)(host_virtual_addr);
            m_vta_chunk.guest_bytes_addr = host_virtual_addr;
        }

        inline tval& operator[](UInt idx) {
            vassert(idx < MAX_TMP);
            return *reinterpret_cast<tval*>(&m_ir_temp_trunk[idx * tval_align_size]);
            //return reinterpret_cast<tval*>(&m_ir_temp_trunk)[idx];
        }
        inline VexTranslateArgs* get_ir_vex_translate_args() { return &m_vta_chunk; }
        inline VexGuestExtents* get_ir_vex_guest_extents() { return &m_vge_chunk; }

        inline void block_integrity(Addr address, UInt insn_block_delta) {
            Addr delta = (address)-m_guest_start_of_block;
            if (delta > 0 && delta < insn_block_delta) {
                vex_printf("\n********* code: %p has been patched!! *********\n", (address));
                m_is_dynamic_block = true;
            }
        }
        inline bool check() { return m_is_dynamic_block; };

        ~EmuEnvironment();
    };


};


#endif  //! _ENV_VEX_;