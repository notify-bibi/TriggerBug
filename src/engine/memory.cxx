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

#include "engine/memory.h"
using namespace TR;

mem_trace Mem::default_trace;


PAGE_DATA* PAGE_DATA::get_write_page(int user, PAGE* pt[1], z3::vcontext& ctx)
{
    if (user == m_user) 
        return this;
    vassert(pt[0] == this);
    pt[0]->dec_used_ref();
    PAGE_DATA* page = new PAGE_DATA(user, *this, ctx);
    pt[0] = page;
    return page;
}



PAGE_DATA* PAGE_PADDING::get_write_page(int user, PAGE* pt[1], z3::vcontext& ctx)
{
    vassert(pt[0] == this);
    PAGE_DATA* res = new PAGE_DATA(user, ctx, get_padding_value());
    if (user == m_user) {
        dec_used_ref();
        delete pt[0];
    }
    else {
        dec_used_ref();
    }
    pt[0] = res;
    return res;
}


PAGE* TR::MBase::get_write_page(HWord address)
{
    PAGE** pt = this->get_pointer_of_mem_page(address);
    PAGE* page = (pt) ? pt[0] : nullptr;
    MEM_ACCESS_ASSERT_W(page, address);
    PAGE* res = page->get_write_page(m_user, pt, m_ctx);
    res->check_ref_cound(1);
    return res;
}


template <typename HWord>
static const UChar* guest_insn_control_method_imp(void* instance, Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code) {
    MEM* mem = (MEM*)instance;
    return mem->guest_insn_control(guest_IP_sbstart, delta, guest_code);
}



PAGE* TR::MBase::map_interface(ULong address) {
    return new PAGE_PADDING(get_user(), 0xCC);;
}

void TR::MBase::copy_interface(PAGE* pt_dst[1], PAGE* pt_src[1]) {
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

void TR::MBase::unmap_interface(PAGE* pt[1]) {
    PAGE* page = pt[0];
    page->dec_used_ref();
    if (page->get_user() == m_user) {
        page->check_ref_cound(0);
        delete page;
        pt[0] = nullptr;
    }else{
        vassert(page->get_used_ref() >= 1);
    }
}

PAGE_DATA* PAGE_PADDING::convert_to_data(PAGE* pt[1], z3::vcontext& ctx)
{
    vassert(pt[0]->is_padding());
    PAGE_PADDING* p_bak = (PAGE_PADDING*)pt[0];
    PAGE_DATA* res = new PAGE_DATA(p_bak->get_user(), ctx, p_bak->get_padding_value());
    if UNLIKELY(p_bak->dec_used_ref()==0) {
       delete p_bak;
    }
    pt[0] = res;
    return res;
}




ULong TR::MBase::find_block_forward(ULong start, HWord size) {
    start &= ~0xfffull;
    HWord get_mem = 0;
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

ULong TR::MBase::find_block_reverse(ULong start, HWord size)
{
    start &= ~0xfffull;
    HWord get_mem = 0;
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

const UChar* TR::MBase::get_vex_insn_linear(Addr guest_IP_sbstart)
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

const UChar* TR::MBase::libvex_guest_insn_control(Addr guest_IP_sbstart, Long delta, const UChar* guest_code)
{
    guest_IP_sbstart += delta;
    if (0x756EEFC5 == guest_IP_sbstart) {
        printf("bkp");
    }
    UInt the_rest_n = 0x1000 - (guest_IP_sbstart & 0xfff);
    Insn_linear& insn_linear = this->m_insn_linear;
    vassert(insn_linear.insn_block_delta <= delta);
    insn_linear.insn_block_delta = delta;
    static constexpr UInt size_swap = sizeof(Insn_linear::swap);
    static constexpr UInt Threshold = size_swap/2;
    if LIKELY(insn_linear.flag == enough) {
        if UNLIKELY(the_rest_n <= Threshold) {

            PAGE* p = get_mem_page(guest_IP_sbstart);
            MEM_ACCESS_ASSERT_R(p, guest_IP_sbstart);

            PAGE* next_p = get_mem_page(guest_IP_sbstart + 0x1000);
            MEM_ACCESS_ASSERT_R(next_p, guest_IP_sbstart + 0x1000);
            next_p->set_code_flag();


            insn_linear.flag = swap_state;
            const UChar* align_address = (const UChar*)pto_data(p)->get_bytes(0x1000 - Threshold);
            
            memcpy(insn_linear.swap, align_address, Threshold);
            memcpy(insn_linear.swap + Threshold, pto_data(next_p)->get_bytes(0), Threshold);
            const UChar* ret_guest_code = (unsigned char*)(insn_linear.swap + (Threshold - the_rest_n)) - delta;
            return ret_guest_code;
        }
    }
    else if UNLIKELY(insn_linear.flag == swap_state) {
        ULong offset = ((delta + guest_code) - insn_linear.swap);
        if UNLIKELY(offset<= size_swap && offset >= Threshold) {
            insn_linear.flag = enough;
            PAGE* p = get_mem_page(guest_IP_sbstart);
            MEM_ACCESS_ASSERT_R(p, guest_IP_sbstart);
            p->set_code_flag();
            return (const UChar*)pto_data(p)->get_bytes((offset - Threshold)) - delta;
        }
    }
    
    return guest_code;

    

}


TR::MBase::MBase(z3::solver& s, z3::vcontext& ctx, PML4T** cr3, Int _user, Bool _need_record)
    :
    m_user(_user),
    m_ctx(ctx),
    m_solver(s),
    m_need_record(_need_record)
{
    CR3[0] = cr3[0];
}
TR::MBase::MBase(z3::solver& so, z3::vcontext& ctx, Bool _need_record)
    :
    m_user(0),
    m_ctx(ctx),
    m_solver(so),
    m_need_record(_need_record)
{
}

TR::MBase::MBase(z3::solver& so, z3::vcontext& ctx, MBase& father_mem, Bool _need_record)
    :
    m_user(((Int)father_mem.m_user) + 1),
    m_ctx(ctx),
    m_solver(so),
    m_need_record(_need_record)
{
    vassert(this->m_user != father_mem.m_user);
    this->copy(father_mem.CR3[0]);
}

bool TR::MBase::checkup_page_ref(PAGE*& P, PAGE** PT)
{
#ifndef CLOSECNW
    if LIKELY(m_user == P->get_user()) {
#ifdef USECNWNOAST
        mem_change_map[ALIGN(address, 0x1000)] = (*P);
#endif
        if UNLIKELY(P->is_padding()) {
            P = pto_padding(P)->convert_to_data(PT, m_ctx);
        }
        return false;
    }
    else {
        P->dec_used_ref();
        PAGE* np;
        if UNLIKELY(P->is_padding()) {
            np = new PAGE_DATA(get_user(), m_ctx, pto_padding(P)->get_padding_value());
        }
        else {
            np = new PAGE_DATA(get_user(), *pto_data(P), m_ctx);
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

static void _init_page(TR::MBase* m, PAGE*& P, HWord address)
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

#define init_page(ref, addr) _init_page(this, ref, addr)
//very fast this api have no record
UInt TR::MBase::write_bytes(ULong address, ULong length, UChar* data) {
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
                pto_data(p_page)->get_writer().set(address & 0xfff, data[count]);
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
            pto_data(p_page)->get_writer().Ist_Put(address & 0xfff, data, align_l);
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
                for (HWord idx = 0; idx < smax; idx += 32) {
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
                    p_page = ((PAGE_PADDING*)p_page)->convert_to_data(p_pt, m_ctx);
                }
                else {
                    pto_padding(p_page)->set_padding_value(M256i(pad).m256i_u8[0]);
                    count = ALIGN(address + count + 0x1000, 0x1000) - address;
                    continue;
                }
            }
        }
        pto_data(p_page)->get_writer().set((address + count) & 0xfff, _mm256_loadu_si256((__m256i*) (data + count)));
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
            if (p_page->is_padding()) {
                p_page = ((PAGE_PADDING*)p_page)->convert_to_data(p_pt, m_ctx);
            }
            pto_data(p_page)->get_writer().Ist_Put((address + count) & 0xfff, &data[count], align_r);
            write_count += align_r;
        }
        else {
            pto_padding(p_page)->set_padding_value(M256i(pad).m256i_u8[0]);
        }
    }

    return write_count;
}



sv::tval Mem::_Iex_Load(PAGE* P, HWord address, UShort size)
{
    PAGE* nP = get_mem_page(address + 0x1000);
    MEM_ACCESS_ASSERT_R(nP, address + 0x1000);
    UInt plength = 0x1000 - ((UShort)address & 0xfff);

    sv::tval L = pto_data(nP)->Iex_Get(m_user, 0, size - plength, m_ctx);
    sv::tval R = pto_data(P)->Iex_Get(m_user, ((UShort)address & 0xfff), plength, m_ctx);
    return L.concat(R);
}
;


sv::tval Mem::Iex_Load(HWord address, IRType ty)
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



template<int ea_nbits>
sv::tval Mem::Iex_Load(const subval<ea_nbits>& address, IRType ty) {
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


sv::tval Mem::Iex_Load(const sv::tval& address, IRType ty)
{
    if (address.nbits() == 32) {
        if (address.real()) {
            return Iex_Load((HWord)address.tor<false, 32>(), ty);
        }
        else {
            return Iex_Load(address.tos<false, 32>(), ty);
        }
    }
    else {
        if (address.real()) {
            return Iex_Load((HWord)address.tor<false, 64>(), ty);
        }
        else {
            return Iex_Load(address.tos<false, 64>(), ty);
        }
    }
}

sv::tval Mem::Iex_Load(const sv::tval& address, int nbits)
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


void TR::Mem::Ist_Store(HWord address, sv::tval const& data)
{
    if (data.real()) {
        switch (data.nbits()) {
        case 8:  { store(address, (uint8_t)data); return; }
        case 16: { store(address, (uint16_t)data); return; }
        case 32: { store(address, (uint32_t)data); return; }
        case 64: { store(address, (uint64_t)data); return; }
        case 128:{ store(address, (__m128i)data); return; }
        case 256:{ store(address, (__m256i)data); return; }
        default:
            VPANIC("not support");
        };
    }
    else {
        switch (data.nbits()) {
        case 8:  { store(address, data.tos<false, 8>()); return; }
        case 16: { store(address, data.tos<false, 16>()); return; }
        case 32: { store(address, data.tos<false, 32>()); return; }
        case 64: { store(address, data.tos<false, 64>()); return; }
        case 128:{ store(address, data.tos<false, 128>()); return; }
        case 256:{ store(address, data.tos<false, 256>()); return; }
        default:
            VPANIC("not support");
        };
    }
}

void TR::Mem::Ist_Store(sv::tval const& address, sv::tval const& data)
{
    if LIKELY(address.real()) {
        if (address.nbits() == 32) {
            Ist_Store((HWord)address.tor<false, 32>(), data);
        }
        else {
            Ist_Store((HWord)address.tor<false, 64>(), data);
        }
    }
    else {
        if (address.nbits() == 32) {
            Ist_Store(address.tos<false, 32>(), data);
        }
        else {
            Ist_Store(address.tos<false, 64>(), data);
        }
    }
}


template<int ea_nbits>
void TR::Mem::Ist_Store(const subval<ea_nbits>& address, sv::tval const& data)
{
    if (data.real()) {
        switch (data.nbits()) {
        case 8: { store(address, (uint8_t)data); return; }
        case 16: { store(address, (uint16_t)data); return; }
        case 32: { store(address, (uint32_t)data); return; }
        case 64: { store(address, (uint64_t)data); return; }
        case 128: { store(address, (__m128i)data); return; }
        case 256: { store(address, (__m256i)data); return; }
        default:
            VPANIC("not support");
        };
    }
    else {
        switch (data.nbits()) {
        case 8: { store(address, data.tos<false, 8, Z3_BV_SORT>()); return; }
        case 16: { store(address, data.tos<false, 16, Z3_BV_SORT>()); return; }
        case 32: { store(address, data.tos<false, 32, Z3_BV_SORT>()); return; }
        case 64: { store(address, data.tos<false, 64, Z3_BV_SORT>()); return; }
        case 128: { store(address, data.tos<false, 128, Z3_BV_SORT>()); return; }
        case 256: { store(address, data.tos<false, 256, Z3_BV_SORT>()); return; }
        default:
            VPANIC("not support");
        };
    }
}



static ULong genericg_compute_checksum_8al(HWord first_w64, HWord n_w64s)
{
    ULong  sum1 = 0, sum2 = 0;
    ULong* p = (ULong*)first_w64;
    /* unrolled */
    while (n_w64s >= 4) {
        ULong  w;
        w = p[0];  sum1 = __rolq(sum1 ^ w, 63);  sum2 += w;
        w = p[1];  sum1 = __rolq(sum1 ^ w, 63);  sum2 += w;
        w = p[2];  sum1 = __rolq(sum1 ^ w, 63);  sum2 += w;
        w = p[3];  sum1 = __rolq(sum1 ^ w, 63);  sum2 += w;
        p += 4;
        n_w64s -= 4;
        sum1 ^= sum2;
    }
    while (n_w64s >= 1) {
        ULong  w;
        w = p[0];  sum1 = __rolq(sum1 ^ w, 63);  sum2 += w;
        p += 1;
        n_w64s -= 1;
        sum1 ^= sum2;
    }
    return sum1 + sum2;
}




ULong TR::MBase::genericg_compute_checksum(HWord base2check, UInt len2check)
{
    HWord first_hW = ALIGN(((HWord)base2check), 8);
    HWord last_hW = ALIGN((((HWord)base2check) + len2check - 1), 8);
    vassert(first_hW <= last_hW);
    HWord hW_diff = last_hW - first_hW;
    HWord hWs_to_check = (hW_diff + 8) / 8;
    vassert(hWs_to_check > 0);


    UInt n_w64s = hWs_to_check;

    HWord L_idx = first_hW;
    HWord R_idx = ALIGN(last_hW, 0x1000);
    ULong checksum = 0;
    UInt spend = ((R_idx - L_idx) % (0x1000)) >> 3;
    while (n_w64s != 0) {
        PAGE* page = get_mem_page(L_idx);
        const UChar* data_base = pto_data(page)->get_bytes(0);
        if(n_w64s < spend) spend = n_w64s;
        checksum = checksum ^ genericg_compute_checksum_8al((HWord)data_base + (L_idx & 0xfff), spend);
        n_w64s -= spend;
        L_idx += spend << 3;
        spend = 0x1000/8;
    }
    return checksum;

}







template void TR::Mem::Ist_Store(const subval<32>& address, sv::tval const& data);
template void TR::Mem::Ist_Store(const subval<64>& address, sv::tval const& data);
