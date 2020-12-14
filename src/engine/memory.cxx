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


template <typename THword>
static const UChar* guest_insn_control_method_imp(void* instance, Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code) {
    MEM<THword>* mem = (MEM<THword>*)instance;
    return mem->guest_insn_control(guest_IP_sbstart, delta, guest_code);
}



template<typename THword>
PAGE* MEM<THword>::map_interface(ULong address) {
    return new PAGE(user);;
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
        delete page;
        pt[0] = 0;
    }
}


template<typename THword>
MEM<THword>::MEM(vctx_base& vctx, z3::solver& so, z3::vcontext& ctx, Bool _need_record) :
    m_vctx(vctx),
    m_solver(so),
    m_ctx(ctx),
    need_record(_need_record),
    user(vctx.mk_user_id())
{
}

template<typename THword>
MEM<THword>::MEM(z3::solver& so, z3::vcontext& ctx, MEM& father_mem, Bool _need_record) :
    m_vctx(father_mem.m_vctx),
    m_solver(so),
    m_ctx(ctx),
    need_record(_need_record),
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
    const UChar* guest_addr_in_page = (const UChar*)(*p)->m_bytes + (guest_IP_sbstart & 0xfff);
    this->m_insn_linear = Insn_linear{
        .flag = enough,
        .the_rest_n = 0x1000 - (UInt)(guest_IP_sbstart & 0xfff),
        .guest_addr_in_page = guest_addr_in_page,
        .guest_block_start = guest_IP_sbstart,
        .insn_block_delta = -1

    };
    const UChar* res = this->libvex_guest_insn_control(guest_IP_sbstart, 0, guest_addr_in_page);
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
            insn_linear.flag = swap_state;
            const UChar* align_address = insn_linear.guest_addr_in_page + the_rest_n - 0x10;
            const UChar* now_address = insn_linear.guest_addr_in_page + delta;
            *(__m128i*)(insn_linear.swap) = *(__m128i*)(align_address);
            *(__m128i*)(insn_linear.swap + 16) = *(__m128i*)(this->get_next_page(guest_IP_sbstart));
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
    tval L, R;
    if (user == nP->get_user()) {
        L = (*nP)->Iex_Get(0, size - plength);
    }
    else {
        L = (*nP)->Iex_Get(0, size - plength, m_ctx);
    }

    if (user == P->get_user()) {
        R = (*P)->Iex_Get(((UShort)address & 0xfff), plength);
    }
    else {
        R = (*P)->Iex_Get(((UShort)address & 0xfff), plength, m_ctx);
    }
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
bool MEM<THword>::check_page(PAGE*& P, PAGE** PT)
{
#ifndef CLOSECNW
    Int xchg_user = 0;
    P->lock(xchg_user);
    if (user == xchg_user) {
        P->unlock(xchg_user);
#ifdef USECNWNOAST
        mem_change_map[ALIGN(address, 0x1000)] = (*P);
#endif
        P->disable_pad(m_ctx, need_record);
        return false;
    }
    P->dec_used_ref();
    if (user == PT[0]->get_user()) {
        VPANIC("ERROR");
    }

    P->unlock(xchg_user);

    PAGE* np = new PAGE(user);
    np->copy(P, m_ctx, need_record);
    PT[0] = np;

    P = np;
#else
    vassert(user == P->user);
    mem_change_map[ALIGN(address, 0x1000)] = (*P);
#endif
    return true;
}

template<typename THword>
PAGE* TR::MEM<THword>::get_write_page(THword address)
{
    CODEBLOCKISWRITECHECK(address);
    PAGE** pt = get_pointer_of_mem_page(address);
    PAGE* page = (pt) ? pt[0] : nullptr;
    MEM_ACCESS_ASSERT_W(page, address);
    if (check_page(page, pt)) {
        mem_change_map[ALIGN(address, 0x1000)] = (*page);
    }
    vassert(page->get_user() == user);
    page->check_ref_cound();
    return page;
}

template<typename THword>
void MEM<THword>::init_page(PAGE*& P, THword address)
{
    Int xchg_user = 0;
    P->lock(xchg_user);
    if (user == xchg_user) {
        P->unlock(xchg_user);
        return;
    }
    PAGE** page = get_pointer_of_mem_page(address);
    //P->check_ref_cound();
    P->dec_used_ref();
    PAGE* np = new PAGE(user);
    page[0] = np;
    P->unlock(xchg_user);
    P = np;
    return;
}

static bool sse_cmp(__m256i& pad, void* data, unsigned long size) {
    int index;
    if (!size) return true;
    if (ctz(index, _mm256_movemask_epi8(_mm256_cmpeq_epi8(pad, _mm256_loadu_si256((__m256i*)data))))) {
        return index == size - 1;
    }
    return false;
}

//very fast this api have no record
template<typename THword>
UInt MEM<THword>::write_bytes(ULong address, ULong length, UChar* data) {
    UInt write_count = 0;
    if (length < 32) {
        {
            ULong max = address + length;
            PAGE* p_page = get_mem_page(address);
            MEM_ACCESS_ASSERT_W(p_page, address);
            init_page(p_page, address);
            p_page->malloc_unit(m_ctx, need_record);
            UInt count = 0;
            while (address < max) {
                if (!(address % 0x1000)) {
                    p_page = get_mem_page(address);
                    MEM_ACCESS_ASSERT_W(p_page, address);
                    init_page(p_page, address);
                    p_page->malloc_unit(m_ctx, need_record);
                }
                (*p_page)->m_bytes[address & 0xfff] = data[count];
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
        if (!sse_cmp(pad, data, align_l) || !p_page->is_pad()) {
            p_page->malloc_unit(m_ctx, need_record);
            first_flag = true;
            memcpy(&(*p_page)->m_bytes[address & 0xfff], data, align_l);
            write_count += align_l;
        }
        data += align_l;
        address += align_l;
        length -= align_l;
    }
    UInt count = 0;
    ULong max = (ALIGN(address + length, 32) - address);
    PAGE* p_page = nullptr;

    bool need_mem = false;
    bool need_check = true;
    while (count < max) {
        if ((!((address + count) & 0xfff)) || (need_check)) {
            p_page = get_mem_page(address + count);
            MEM_ACCESS_ASSERT_W(p_page, address + count);
            init_page(p_page, address + count);
            ULong smax = (count + 0x1000 <= max) ? 0x1000 : max - count;
            need_mem = false;
            if (p_page->is_pad()) {
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
                if (need_mem) {
                    p_page->malloc_unit(m_ctx, need_record);
                }
                else {
                    p_page->set_pad(M256i(pad).m256i_u8[0]);
                    count = ALIGN(address + count + 0x1000, 0x1000) - address;
                    continue;
                }
            }
        }
        SET32((&(*p_page)->m_bytes[(address + count) & 0xfff]), *(__m256i*)(data + count));
        count += 32;
        write_count += 32;
    };
    if (align_r) {
        if ((!((address + count) & 0xfff)) || !p_page) {
            p_page = get_mem_page(address + count);
            MEM_ACCESS_ASSERT_W(p_page, address + count);
            init_page(p_page, address + count);
            pad = _mm256_set1_epi8(data[count]);
        }
        if ((!sse_cmp(pad, data + count, align_r)) || need_mem || !p_page->is_pad()) {
            p_page->malloc_unit(m_ctx, need_record);
            memcpy(&(*p_page)->m_bytes[(address + count) & 0xfff], &data[count], align_r);
            write_count += align_r;
        }
        else {
            p_page->set_pad(M256i(pad).m256i_u8[0]);
        }
    }

    return write_count;
}


template class TR::MEM<Addr32>;
template class TR::MEM<Addr64>;
