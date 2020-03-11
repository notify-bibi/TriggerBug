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





template<typename ADDR>
PAGE* MEM<ADDR>::map_interface(ULong address) {
    return new PAGE(user);;
}

template<typename ADDR>
void MEM<ADDR>::copy_interface(PAGE* pt_dst[1], PAGE* pt_src[1]) {
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

template<typename ADDR>
void MEM<ADDR>::unmap_interface(PAGE* pt[1]) {
    PAGE* page = pt[0];
    page->dec_used_ref();
    if (page->get_user() == user) {
        delete page;
        pt[0] = 0;
    }
}


template<typename ADDR>
MEM<ADDR>::MEM(vctx_base& vctx, z3::solver& so, z3::vcontext& ctx, Bool _need_record) :
    m_vctx(vctx),
    m_solver(so),
    m_ctx(ctx),
    need_record(_need_record),
    user(vctx.mk_user_id())
{
}

template<typename ADDR>
MEM<ADDR>::MEM(z3::solver& so, z3::vcontext& ctx, MEM& father_mem, Bool _need_record) :
    m_vctx(father_mem.m_vctx),
    m_solver(so),
    m_ctx(ctx),
    need_record(_need_record),
    user(m_vctx.mk_user_id())
{
    vassert(this->user != father_mem.user);
    this->copy(father_mem.CR3[0]);
}


template<typename ADDR>
void MEM<ADDR>::clearRecord()
{
    for (auto p : mem_change_map) {
        p.second->clearRecord();
    }
    mem_change_map.clear();
}

template<typename ADDR>
ULong MEM<ADDR>::find_block_forward(ULong start, ADDR size) {
    start &= ~0xfffull;
    ADDR get_mem = 0;
    for (; get_mem < size; start += 0x1000) {
        PAGE* p = getMemPage(start);
        if (p) {
            get_mem = 0;
        }
        else {
            get_mem += 0x1000;
        }
    }
    return start -= 0x1000;


}

template<typename ADDR>
ULong MEM<ADDR>::find_block_reverse(ULong start, ADDR size)
{
    start &= ~0xfffull;
    ADDR get_mem = 0;
    for (; get_mem < size; start -= 0x1000) {
        PAGE* p = getMemPage(start);
        if (p) {
            get_mem = 0;
        }
        else {
            get_mem += 0x1000;
        }
    }
    return start += 0x1000;
}
;

template<typename ADDR>
Vns MEM<ADDR>::Iex_Load(ADDR address, IRType ty)
{
    switch (ty) {
    case 8:
    case Ity_I8: return Iex_Load<Ity_I8>(address);
    case 16:
    case Ity_I16: return Iex_Load<Ity_I16>(address);
    case 32:
    case Ity_F32:
    case Ity_I32:return Iex_Load<Ity_I32>(address);
    case 64:
    case Ity_F64:
    case Ity_I64:return Iex_Load<Ity_I64>(address);
    case 128:
    case Ity_I128:
    case Ity_V128:return Iex_Load<Ity_V128>(address);
    case 256:
    case Ity_V256:return Iex_Load<Ity_V256>(address);
    default:VPANIC("2333333");
    }
}

template<typename ADDR>
Vns MEM<ADDR>::Iex_Load(Z3_ast address, IRType ty) {
    switch (ty) {
    case 8:
    case Ity_I8: return Iex_Load<Ity_I8>(address);
    case 16:
    case Ity_I16:return Iex_Load<Ity_I16>(address);
    case 32:
    case Ity_F32:
    case Ity_I32:return Iex_Load<Ity_I32>(address);
    case 64:
    case Ity_F64:
    case Ity_I64:return Iex_Load<Ity_I64>(address);
    case 128:
    case Ity_I128:
    case Ity_V128:return Iex_Load<Ity_V128>(address);
    case 256:
    case Ity_V256:return Iex_Load<Ity_V256>(address);
    default:
        VPANIC("2333333");
    }
}

template<typename ADDR>
void MEM<ADDR>::CheckSelf(PAGE*& P, ADDR address)
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
        return;
    }
    //--P->used_point;
    //P->check_ref_cound();
    P->dec_used_ref();
    PAGE** page = get_pointer_of_mem_page(address);
    vassert(user != (*page)->get_user());
    PAGE* np = new PAGE(user);
    np->copy(P, m_ctx, need_record);
    *page = np;
    P->unlock(xchg_user);
    P = np;
    mem_change_map[ALIGN(address, 0x1000)] = (*np);
#else
    vassert(user == P->user);
    mem_change_map[ALIGN(address, 0x1000)] = (*P);
#endif
}

template<typename ADDR>
void MEM<ADDR>::init_page(PAGE*& P, ADDR address)
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
    unsigned long index;
    if (!size) return true;
    if (_BitScanForward(&index, _mm256_movemask_epi8(_mm256_cmpeq_epi8(pad, _mm256_loadu_si256((__m256i*)data))))) {
        return index == size - 1;
    }
    return false;
}

//very fast this api have no record
template<typename ADDR>
UInt MEM<ADDR>::write_bytes(ULong address, ULong length, UChar* data) {
    UInt write_count = 0;
    if (length < 32) {
        {
            ULong max = address + length;
            PAGE* p_page = getMemPage(address);
            MEM_ACCESS_ASSERT_W(p_page, address);
            init_page(p_page, address);
            p_page->malloc_unit(m_ctx, need_record);
            UInt count = 0;
            while (address < max) {
                if (!(address % 0x1000)) {
                    p_page = getMemPage(address);
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
        PAGE* p_page = getMemPage(address);
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
            p_page = getMemPage(address + count);
            MEM_ACCESS_ASSERT_W(p_page, address + count);
            init_page(p_page, address + count);
            ULong smax = (count + 0x1000 <= max) ? 0x1000 : max - count;
            need_mem = false;
            if (p_page->is_pad()) {
                if (!need_check) {
                    pad = _mm256_set1_epi8(data[count]);
                }
                for (ADDR idx = 0; idx < smax; idx += 32) {
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
                    p_page->set_pad(pad.m256i_u8[0]);
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
            p_page = getMemPage(address + count);
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
            p_page->set_pad(pad.m256i_u8[0]);
        }
    }

    return write_count;
}

template MEM<Addr32>;
template MEM<Addr64>;
