/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    Memory.class:
Abstract:
    Address mapping technique;
    Copy-on-Write;
    Fork technology;
    符号地址存取;
Author:
    WXC 2019-05-31.
Revision History:
--*/

#define UNDEFMEM
#include "engine/memory.h"
using namespace TR;

template<typename THword>
PAGE* TR::MEM<THword>::get_write_page(THword address)
{
    PAGE** pt = get_pointer_of_mem_page(address);
    PAGE* page = (pt) ? pt[0] : nullptr;
    MEM_ACCESS_ASSERT_W(page, address);

    //检查是否将ir translate的block区代码修改了，避免某些vmp或者ctf的恶作剧
    if UNLIKELY(m_ee) {
        m_ee->block_integrity(page->is_code(), address, this->m_insn_linear.insn_block_delta);
    }

    if UNLIKELY(checkup_page_ref(page, pt)) {
        mem_change_map[ALIGN(address, 0x1000)] = &pto_data(page)->get_unit();
    }
    vassert(page->get_user() == user);
    page->check_ref_cound(1);
    return page;
}


template <typename THword>
static const UChar* guest_insn_control_method_imp(void* instance, Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code) {
    MEM<THword>* mem = (MEM<THword>*)instance;
    return mem->guest_insn_control(guest_IP_sbstart, delta, guest_code);
}



template<typename THword>
PAGE* MEM<THword>::map_interface(ULong address) {
    return new PAGE_PADDING(get_user(), 0xCC);;
}

template<typename THword>
void MEM<THword>::copy_interface(PAGE* pt_dst[1], PAGE* pt_src[1]) {
#ifndef CLOSECNW
#ifdef USECNWNOAST
    PAGE* fpage = pt_src[0];
    if (!fpage->is_pad) {
        if (fpage->unit->symbolic) {
            PAGE* page = new PAGE;
            pt_dst[0] = page;
            page->unit_mutex = true;
            page->used_point = 1;
            page->user = user;
            page->unit = new Register<0x1000>(*(fpage->unit), m_ctx, need_record);
            page->is_pad = false;
            goto dont_use_father_page;
        }
    }
    pt_dst[0] = pt_src[0];//copy
    inc_used_ref((pt_dst[0]));
dont_use_father_page:
#else
    pt_dst[0] = pt_src[0];//copy
    pt_dst[0]->inc_used_ref();
#endif
#else
    PAGE* fpage = pt_src[0];
    PAGE* page = new PAGE;
    pt_dst[0] = page;
    page->unit_mutex = true;
    page->used_point = 1;
    page->user = user;
    if (fpage->is_pad) {
        page->unit = NULL;
        page->is_pad = true;
        page->pad = fpage->pad;
    }
    else {
        page->unit = new Register<0x1000>(*(fpage->unit), m_ctx, need_record);
        page->is_pad = false;
    }
#endif

}

template<typename THword>
void MEM<THword>::unmap_interface(PAGE* pt[1]) {
    PAGE* page = pt[0];
    page->dec_used_ref();
    if (page->get_user() == user) {
        page->check_ref_cound(0);
        if (page->is_padding()) {
            delete pto_padding(page);
        }
        else {
            delete pto_data(page);
        }
        
        pt[0] = nullptr;
    }else{
        vassert(page->get_used_ref() >= 1);
    }
}

PAGE_DATA* PAGE_PADDING::convert_to_data(PAGE* pt[1], z3::vcontext& ctx, bool nr)
{

    PAGE_PADDING* p_bak = (PAGE_PADDING*)pt[0];
    vassert(pt[0]->is_padding());
    PAGE_DATA* res = new PAGE_DATA(p_bak->get_user(), ctx, nr, p_bak->get_padding_value());
    if UNLIKELY(p_bak->dec_used_ref()==0) {
        if (((PAGE*)p_bak)->is_padding()) {
            delete pto_padding(p_bak);
        }
        else {
            delete pto_data(p_bak);
        }
    }
    pt[0] = res;
    return res;
}


template<typename THword>
MEM<THword>::MEM(vctx_base& vctx, z3::solver& so, z3::vcontext& ctx, Bool _need_record) :
    m_vctx(vctx),
    m_ctx(ctx),
    need_record(_need_record),
    m_solver(so),
    user(vctx.mk_user_id())
{
}

template<typename THword>
MEM<THword>::MEM(z3::solver& so, z3::vcontext& ctx, MEM& father_mem, Bool _need_record) :
    m_vctx(father_mem.m_vctx),
    m_ctx(ctx),
    need_record(_need_record),
    m_solver(so),
    user(m_vctx.mk_user_id())
{
    vassert(this->user != father_mem.user);
    this->copy(father_mem.CR3[0]);
}


template<typename THword>
void MEM<THword>::clearRecord()
{
    for (auto p : mem_change_map) {
        p.second->clearRecord();
    }
    mem_change_map.clear();
}

template<typename THword>
ULong MEM<THword>::find_block_forward(ULong start, THword size) {
    start &= ~0xfffull;
    THword get_mem = 0;
    for (; get_mem < size; start += 0x1000) {
        PAGE* p = get_mem_page(start);
        if (p) {
            get_mem = 0;
        }
        else {
            get_mem += 0x1000;
        }
    }
    return start -= 0x1000;


}

template<typename THword>
ULong MEM<THword>::find_block_reverse(ULong start, THword size)
{
    start &= ~0xfffull;
    THword get_mem = 0;
    for (; get_mem < size; start -= 0x1000) {
        PAGE* p = get_mem_page(start);
        if (p) {
            get_mem = 0;
        }
        else {
            get_mem += 0x1000;
        }
    }
    return start += 0x1000;
}

template<typename THword>
const UChar* TR::MEM<THword>::get_vex_insn_linear(Addr guest_IP_sbstart)
{
    PAGE* p = get_mem_page(guest_IP_sbstart);
    MEM_ACCESS_ASSERT_R(p, guest_IP_sbstart);
    const UChar* guest_addr_in_page = (const UChar*)pto_data(p)->get_bytes(guest_IP_sbstart & 0xfff);
    this->m_insn_linear = Insn_linear{
        .flag = enough,
        .the_rest_n = 0x1000 - (UInt)(guest_IP_sbstart & 0xfff),
        .guest_addr_in_page = guest_addr_in_page,
        .guest_block_start = guest_IP_sbstart,
        .insn_block_delta = -1

    };
    const UChar* res = this->libvex_guest_insn_control(guest_IP_sbstart, 0, guest_addr_in_page);
    p->set_code_flag();
    return res;
}

template<typename THword>
const UChar* TR::MEM<THword>::libvex_guest_insn_control(Addr guest_IP_sbstart, Long delta, const UChar* guest_code)
{

    Addr the_rest_n = 0x1000 - (guest_IP_sbstart & 0xfff);
    Insn_linear& insn_linear = this->m_insn_linear;
    vassert(insn_linear.insn_block_delta <= delta);
    insn_linear.insn_block_delta = delta;
    
    if (insn_linear.flag == enough) {
        if (the_rest_n - delta <= 16) {
            PAGE* next_p = get_mem_page(guest_IP_sbstart + 0x1000);
            MEM_ACCESS_ASSERT_R(next_p, guest_IP_sbstart + 0x1000);
            next_p->set_code_flag();

            insn_linear.flag = swap_state;
            const UChar* align_address = insn_linear.guest_addr_in_page + the_rest_n - 0x10;
            const UChar* now_address = insn_linear.guest_addr_in_page + delta;
            *(__m128i*)(insn_linear.swap) = *(__m128i*)(align_address);
            *(__m128i*)(insn_linear.swap + 16) = *(__m128i*)(pto_data(next_p)->get_bytes(0));
            //delta = (insn_linear.swap + (now_address - align_address)) - guest_code;
            const UChar* ret_guest_code = (unsigned char*)(insn_linear.swap + (now_address - align_address)) - delta;
            return ret_guest_code;
        }
    }
    else if (insn_linear.flag == swap_state) {
        ULong offset = ((delta + guest_code) - insn_linear.swap);
        if (offset >= 16) {
            insn_linear.flag = next_page;
            vassert((offset <= 32));
            //delta = insn_linear.n_page_mem(insn_linear) + (offset - 16) - guest_code;
            const UChar* ret_guest_code = this->get_next_page(guest_IP_sbstart) + (offset - 16) - delta;
            return ret_guest_code;
        }
    }
    
    return guest_code;

    

}

template<typename THword>
tval TR::MEM<THword>::_Iex_Load(PAGE* P, THword address, UShort size)
{
    PAGE* nP = get_mem_page(address + 0x1000);
    MEM_ACCESS_ASSERT_R(nP, address + 0x1000);
    UInt plength = 0x1000 - ((UShort)address & 0xfff);

    tval L = pto_data(nP)->get_unit().Iex_Get(user, 0, size - plength, m_ctx);
    tval R = pto_data(P)->get_unit().Iex_Get(user, ((UShort)address & 0xfff), plength, m_ctx);
    return L.concat(R);
}
;

template<typename THword>
tval MEM<THword>::Iex_Load(THword address, IRType ty)
{
    switch (ty) {
    case Ity_I8: return load<Ity_I8>(address);
    case Ity_I16: return load<Ity_I16>(address);
    case Ity_F32: return load<Ity_F32>(address);
    case Ity_I32: return load<Ity_I32>(address);
    case Ity_F64: return load<Ity_F64>(address);
    case Ity_I64: return load<Ity_I64>(address);
    case Ity_F128: return load<Ity_F128>(address);
    case Ity_I128: return load<Ity_I128>(address);
    case Ity_V128: return load<Ity_V128>(address);
    case Ity_V256: return load<Ity_V256>(address);
    default:VPANIC("error");
    }
}

template<typename THword>
inline tval TR::MEM<THword>::Iex_Load(const tval& address, IRType ty)
{
    using vc = sv::sv_cty<THword>;
    if (address.real()) {
        return Iex_Load((THword)address.tor<false, wide>(), ty);
    }
    else {
        return Iex_Load((Z3_ast)address.tos<false, wide>(), ty);
    }
}

template<typename THword>
tval TR::MEM<THword>::Iex_Load(const tval& address, int nbits)
{
    switch (nbits) {
    case 8: return load<Ity_I8>(address);
    case 16: return load<Ity_I16>(address);
    case 32: return load<Ity_I32>(address);
    case 64: return load<Ity_I64>(address);
    case 128: return load<Ity_I128>(address);
    case 256: return load<Ity_V256>(address);
    default:
        VPANIC("not support");
    }
}

template<typename THword>
tval TR::MEM<THword>::Iex_Load(const sv::rsval<false, wide>& address, IRType ty)
{
    if (address.real()) {
        return Iex_Load((THword)address.tor(), ty);
    }
    else {
        return Iex_Load((Z3_ast)address.tos(), ty);
    }
}

template<typename THword>
tval MEM<THword>::Iex_Load(Z3_ast address, IRType ty) {
    switch (ty) {
    case Ity_I8: return load<Ity_I8>(address);
    case Ity_I16: return load<Ity_I16>(address);
    case Ity_F32: return load<Ity_F32>(address);
    case Ity_I32: return load<Ity_I32>(address);
    case Ity_F64: return load<Ity_F64>(address);
    case Ity_I64: return load<Ity_I64>(address);
    case Ity_F128: return load<Ity_F128>(address);
    case Ity_I128: return load<Ity_I128>(address);
    case Ity_V128: return load<Ity_V128>(address);
    case Ity_V256: return load<Ity_V256>(address);
    default:VPANIC("error");
    }
}

template<typename THword>
void TR::MEM<THword>::Ist_Store(THword address, tval const& data)
{
    if (data.real()) {
        switch (data.nbits()) {
        case 8: store(address, (uint8_t)data); return;
        case 16: store(address, (uint16_t)data); return;
        case 32: store(address, (uint32_t)data); return;
        case 64: store(address, (uint64_t)data); return;
        case 128:store(address, (__m128i)data); return;
        case 256:store(address, (__m256i)data); return;
        default:
            VPANIC("not support");
        };
    }
    else {
        switch (data.nbits()) {
        case 8: store<8>(address, (Z3_ast)data); return;
        case 16: store<16>(address, (Z3_ast)data); return;
        case 32: store<32>(address, (Z3_ast)data); return;
        case 64: store<64>(address, (Z3_ast)data); return;
        case 128:store<128>(address, (Z3_ast)data); return;
        case 256:store<256>(address, (Z3_ast)data); return;
        default:
            VPANIC("not support");
        };
    }


}

template<typename THword>
void TR::MEM<THword>::Ist_Store(Z3_ast address, tval const& data)
{
    if (data.real()) {
        switch (data.nbits()) {
        case 1: store(address, (uint8_t)data); return;
        case 2: store(address, (uint16_t)data); return;
        case 4: store(address, (uint32_t)data); return;
        case 8: store(address, (uint64_t)data); return;
        case 16:store(address, (__m128i)data); return;
        case 32:store(address, (__m256i)data); return;
        default:
            VPANIC("not support");
        };
    }
    else {
        switch (data.nbits()) {
        case 1: store<8>(address, (Z3_ast)data); return;
        case 2: store<16>(address, (Z3_ast)data); return;
        case 4: store<32>(address, (Z3_ast)data); return;
        case 8: store<64>(address, (Z3_ast)data); return;
        case 16:store<128>(address, (Z3_ast)data); return;
        case 32:store<256>(address, (Z3_ast)data); return;
        default:
            VPANIC("not support");
        };
    }

}




template<typename THword>
bool MEM<THword>::checkup_page_ref(PAGE*& P, PAGE** PT)
{
#ifndef CLOSECNW
    if LIKELY(user == P->get_user()) {
#ifdef USECNWNOAST
        mem_change_map[ALIGN(address, 0x1000)] = (*P);
#endif
        if UNLIKELY(P->is_padding()) {
            P = pto_padding(P)->convert_to_data(PT, m_ctx, this->is_need_record());
        }
        return false;
    }
    else {
        P->dec_used_ref();
        PAGE* np;
        if UNLIKELY(P->is_padding()) {
            np = new PAGE_DATA(get_user(), m_ctx, this->is_need_record(), pto_padding(P)->get_padding_value());
        }
        else {
            np = new PAGE_DATA(get_user(), *pto_data(P), m_ctx, this->is_need_record());
        }
        PT[0] = np;
        P = np;
#else
        vassert(user == P->user);
        mem_change_map[ALIGN(address, 0x1000)] = (*P);
#endif
        return true;
    }
}


static bool sse_cmp(__m256i& pad, void* data, unsigned long size) {
    int index;
    if UNLIKELY(!size) return true;
    if LIKELY(ctz(index, _mm256_movemask_epi8(_mm256_cmpeq_epi8(pad, _mm256_loadu_si256((__m256i*)data))))) {
        return index == size - 1;
    }
    return false;
}

template<typename THword>
static void _init_page(MEM<THword>* m, PAGE*& P, THword address)
{

    PAGE** pt = m->get_pointer_of_mem_page(address);
    PAGE* page = (pt) ? pt[0] : nullptr;
    MEM_ACCESS_ASSERT_W(page, address);
    if UNLIKELY(m->get_user() != page->get_user()) {
        page->dec_used_ref();
        page = m->map_interface(address);
        pt[0] = page;
    }
    vassert(page->get_user() == m->get_user());
    page->check_ref_cound(1);
    P = page;
}

#define init_page(ref, addr) _init_page<THword>(this, ref, addr)
//very fast this api have no record
template<typename THword>
UInt MEM<THword>::write_bytes(ULong address, ULong length, UChar* data) {
    UInt write_count = 0;
    if LIKELY(length < 32) {
        {
            ULong max = address + length;
            PAGE* p_page = get_mem_page(address);
            MEM_ACCESS_ASSERT_W(p_page, address);
            init_page(p_page, address);
            //p_page->malloc_unit(m_ctx, need_record);
            UInt count = 0;
            while (address < max) {
                if (!(address % 0x1000)) {
                    p_page = get_mem_page(address);
                    MEM_ACCESS_ASSERT_W(p_page, address);
                    init_page(p_page, address);
                    //p_page->malloc_unit(m_ctx, need_record);
                }
                pto_data(p_page)->get_unit().set(address & 0xfff, data[count]);
                address += 1;
                count += 1;
            };
            return count;
        }
    }
    bool first_flag = false;
    UInt align_l = 32 - (address - ALIGN(address, 32));
    UInt align_r = (address + length - ALIGN(address + length, 32));
    __m256i pad;
    if (align_l == 32) {
    }
    else {
        PAGE* p_page = get_mem_page(address);
        MEM_ACCESS_ASSERT_W(p_page, address);
        init_page(p_page, address);
        pad = _mm256_set1_epi8(data[0]);
        if UNLIKELY(!sse_cmp(pad, data, align_l) || !p_page->is_padding()) {
            //p_page->malloc_unit(m_ctx, need_record);
            first_flag = true;
            pto_data(p_page)->get_unit().Ist_Put(address & 0xfff, data, align_l);
            write_count += align_l;
        }
        data += align_l;
        address += align_l;
        length -= align_l;
    }
    UInt count = 0;
    ULong max = (ALIGN(address + length, 32) - address);
    PAGE* p_page = nullptr;
    PAGE** p_pt = nullptr;

    bool need_mem = false;
    bool need_check = true;
    while (count < max) {
        if ((!((address + count) & 0xfff)) || (need_check)) {
            p_pt = get_pointer_of_mem_page(address + count);
            p_page = p_pt[0];
            MEM_ACCESS_ASSERT_W(p_page, address + count);
            init_page(p_page, address + count);
            ULong smax = (count + 0x1000 <= max) ? 0x1000 : max - count;
            need_mem = false;
            if UNLIKELY(p_page->is_padding()) {
                if (!need_check) {
                    pad = _mm256_set1_epi8(data[count]);
                }
                for (THword idx = 0; idx < smax; idx += 32) {
                    if (!sse_cmp(pad, &data[count + idx], 32)) {
                        need_mem = true;
                        break;
                    }
                }
                if (need_check) {
                    need_check = false;
                    if (first_flag) {
                        need_mem = true;
                    }
                }
                if LIKELY(need_mem) {
                    p_page = ((PAGE_PADDING*)p_page)->convert_to_data(p_pt, m_ctx, need_record);
                }
                else {
                    pto_padding(p_page)->set_padding_value(M256i(pad).m256i_u8[0]);
                    count = ALIGN(address + count + 0x1000, 0x1000) - address;
                    continue;
                }
            }
        }
        pto_data(p_page)->get_unit().set((address + count) & 0xfff, _mm256_loadu_si256((__m256i*) (data + count)));
        count += 32;
        write_count += 32;
    };
    if (align_r) {
        if ((!((address + count) & 0xfff)) || !p_page) {
            p_pt = get_pointer_of_mem_page(address + count);
            p_page = p_pt[0];
            MEM_ACCESS_ASSERT_W(p_page, address + count);
            init_page(p_page, address + count);
            pad = _mm256_set1_epi8(data[count]);
        }
        if ((!sse_cmp(pad, data + count, align_r)) || need_mem || !p_page->is_padding()) {
            p_page = ((PAGE_PADDING*)p_page)->convert_to_data(p_pt, m_ctx, need_record);
            pto_data(p_page)->get_unit().Ist_Put((address + count) & 0xfff, &data[count], align_r);
            write_count += align_r;
        }
        else {
            pto_padding(p_page)->set_padding_value(M256i(pad).m256i_u8[0]);
        }
    }

    return write_count;
}






template class TR::MEM<Addr32>;
template class TR::MEM<Addr64>;

