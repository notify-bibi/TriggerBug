#include "engine/emu_environment.h"
#include "engine/register.h"
#include "engine/memory.h"
#include "engine/kernel.h"
#include "engine/compress.h"
extern "C" {

    void bb_insn_control_obj_set(void* instance, const UChar* (*guest_insn_control_method)(void*, Addr, Long, const UChar*));
}
namespace TR {


    template<unsigned int MAX_TMP>
    template<typename THword>
    EmuEnvironment<MAX_TMP>::EmuEnvironment(vex_info const& info, MEM<THword>& mem_obj, VexArch host)
        :m_info(const_cast<vex_info&>(info)), m_ir_temp_trunk(nullptr) {
        vassert((((size_t)this) & 0xf) == 0);
        vex_info::init_vta_chunk(m_vta_chunk, m_vge_chunk, host, info.gtraceflags());
        bb_insn_control_obj_set((void*)&mem_obj, guest_insn_control_method_imp<THword>);
    }


    template<unsigned int MAX_TMP>
    void EmuEnvironment<MAX_TMP>::malloc_ir_buff(Z3_context ctx)
    {
        vassert(m_ir_temp_trunk == nullptr);
        m_ir_temp_trunk = new UChar[MAX_TMP * tval_align_size];
        for (unsigned j = 0; j < MAX_TMP; j++) { new(&this->operator[](j)) tval(ctx, 0); }
    }

    template<unsigned int MAX_TMP>
    void EmuEnvironment<MAX_TMP>::free_ir_buff()
    {
        vassert(m_ir_temp_trunk != nullptr);
        for (int j = 0; j < MAX_TMP; j++) {
            this->operator[](j).tval::~tval();
        }
        delete m_ir_temp_trunk;
        m_ir_temp_trunk = nullptr;
    }

    template<unsigned int MAX_TMP>
    template<typename THword>
    IRSB* EmuEnvironment<MAX_TMP>::translate_front(MEM<THword>& mem, Addr guest_addr)
    {
        VexRegisterUpdates pxControl;
        VexTranslateResult res;
        VexTranslateArgs* vta = get_ir_vex_translate_args();
        const UChar* bytes_insn = mem.get_vex_insn_linear(guest_addr);
        set_guest_bytes_addr(bytes_insn, guest_addr);
        IRSB* irsb = LibVEX_FrontEnd(vta, &res, &pxControl);
        return irsb;
    }

    template<unsigned int MAX_TMP>
    void EmuEnvironment<MAX_TMP>::set_guest_bytes_addr(const UChar* bytes, Addr64 virtual_addr)
    {
        m_vta_chunk.guest_bytes = bytes;
        m_vta_chunk.guest_bytes_addr = virtual_addr;
        set_start(virtual_addr);
    }
    

    template<unsigned int MAX_TMP>
    template<typename THword>
    void EmuEnvironment<MAX_TMP>::set_guest_code_temp(MEM<THword>& mem_obj, Addr64 virtual_addr, Hook_struct const& hs)
    {
        //*(__m128i*)(m_pap.swap) = mem_obj.load<Ity_V256>(virtual_addr).tor();
        //memcpy(m_pap.swap, &hs.original.m64_u8, hs.nbytes);
#warning "need check"
        //m_pap.start_swap = 2;
        //m_pap.guest_max_insns = 1;
        //m_vta_chunk.guest_bytes = (UChar*)(m_pap.swap);
        m_vta_chunk.guest_bytes_addr = virtual_addr;
    }


    template<unsigned int MAX_TMP>
    EmuEnvironment<MAX_TMP>::~EmuEnvironment()
    {
        vassert(m_ir_temp_trunk == nullptr);
    }
    
    template <typename THword>
    static const UChar* guest_insn_control_method_imp(void* instance, Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code) {
        MEM<THword>* mem = (MEM<THword>*)instance;
        return mem->libvex_guest_insn_control(guest_IP_sbstart, delta, guest_code);
    }
};


template class TR::EmuEnvironment<MAX_IRTEMP>;
template void  TR::EmuEnvironment<MAX_IRTEMP>::set_guest_code_temp(TR::MEM<Addr32>& mem_obj, Addr64 virtual_addr, TR::Hook_struct const& hs);
template void  TR::EmuEnvironment<MAX_IRTEMP>::set_guest_code_temp(TR::MEM<Addr64>& mem_obj, Addr64 virtual_addr, TR::Hook_struct const& hs);
template IRSB* TR::EmuEnvironment<MAX_IRTEMP>::translate_front(TR::MEM<Addr32>& mem_obj, Addr guest_addr);
template IRSB* TR::EmuEnvironment<MAX_IRTEMP>::translate_front(TR::MEM<Addr64>& mem_obj, Addr guest_addr);
template       TR::EmuEnvironment<MAX_IRTEMP>::EmuEnvironment(TR::vex_info const& info, TR::MEM<Addr64>& mem_obj, VexArch host);
template       TR::EmuEnvironment<MAX_IRTEMP>::EmuEnvironment(TR::vex_info const& info, TR::MEM<Addr32>& mem_obj, VexArch host);
