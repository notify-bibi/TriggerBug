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
#include "memory.hpp"
using namespace z3;

unsigned int    global_user = 1;
std::mutex      global_user_mutex;

using namespace z3;

//a=b+c+d+e...+z -> b c d e
template<typename ADDR>
void addressingMode<ADDR>::_offset2opAdd(std::vector<Vns> &ret, expr const& _e)
{
    expr e = _e;
    context& c = e.ctx();
    if (e.kind() == Z3_APP_AST) {
        func_decl f = e.decl();
        switch (f.decl_kind())
        {
        case Z3_OP_BADD: {
            auto max = e.num_args();
            for (UInt i = 0; i < max; i++) {
                _offset2opAdd(ret, e.arg(i));
            }
            return;
        }
        case Z3_OP_BSUB: {
            auto max = e.num_args();
            for (UInt i = 0; i < max; i++) {
                if (i == 0) {
                    _offset2opAdd(ret, e.arg(i));
                }
                else {
                    _offset2opAdd(ret, -e.arg(i));
                }
            }
            return;
        }
        }
        ret.emplace_back(e);
        return;
    }
}

template<typename ADDR>
bool addressingMode<ADDR>::_check_add_no_overflow(expr const& e1, expr const& e2) {
    UInt bs = e1.get_sort().bv_size();
    bool bit_jw = false;
  /*  std::cout << e1 << std::endl;
    std::cout << e2 << std::endl;*/
    for (int i = 0; i < bs; i++) {
        addressingMode::sbit_struct ss0 = addressingMode::_check_is_extract(e1, i);
        addressingMode::sbit_struct ss1 = addressingMode::_check_is_extract(e2, i);
        bool b0 = (ss0.sym_ast) ? true : ss0.rbit;
        bool b1 = (ss1.sym_ast) ? true : ss1.rbit;

        if (b0 ^ b1) {}
        else {
            if (b0 && b1) {
                bit_jw = true;
            }
            else {
                bit_jw = false;
            }
        }
    }
    return !bit_jw;
}

// ast(symbolic address) = numreal(base) + symbolic(offset) 
template<typename ADDR>
expr addressingMode<ADDR>::_ast2base(expr& base,
    expr const& e, 
    UInt deep, UInt max_deep
) {
    context& c = e.ctx();
    if (deep < max_deep) {
        if (e.kind() == Z3_APP_AST) {
            func_decl f = e.decl();
            switch (f.decl_kind())
            {
            case Z3_OP_BADD: {
                expr idx_sum(c);
                auto max = e.num_args();
                for (UInt i = 0; i < max; i++) {
                    expr arg1(c);
                    expr idx = _ast2base(arg1, e.arg(i), deep + 1, max_deep);
                    if ((Z3_ast)idx) {
                        if ((Z3_ast)idx_sum) {
                            idx_sum = idx_sum + idx;
                        }
                        else {
                            idx_sum = idx;
                        }
                    }
                    if ((Z3_ast)arg1) {
                        if ((Z3_ast)base) {
                            base = base + arg1;
                        }
                        else {
                            base = arg1;
                        }
                    }
                }
                return idx_sum;
            }
            case Z3_OP_BSUB: {
                expr idx_sum(c);
                auto max = e.num_args();
                for (UInt i = 0; i < max; i++) {
                    expr arg1(c);
                    expr idx = _ast2base(arg1, e.arg(i), deep + 1, max_deep);
                    if ((Z3_ast)idx) {
                        if ((Z3_ast)idx_sum) {
                            idx_sum = idx_sum - idx;
                        }
                        else {
                            if (i == 0) {
                                idx_sum = idx;
                            }
                            else {
                                idx_sum = -idx;
                            }
                        }
                    }
                    if ((Z3_ast)arg1) {
                        if ((Z3_ast)base) {
                            base = base - arg1;
                        }
                        else {
                            if (i == 0) {
                                base = arg1;
                            }
                            else {
                                base = -arg1;
                            }
                        }
                    }
                }
                return idx_sum;
            }
            case Z3_OP_SIGN_EXT: {
                uint64_t extn = Z3_get_decl_int_parameter(c, f, 0);
                expr arg1(c);
                expr idx1 = _ast2base(arg1, e.arg(0), deep + 1, max_deep);
                if ((Z3_ast)arg1) {
                    if ((Z3_ast)idx1) {
                        UInt bs = idx1.get_sort().bv_size();
                        if (_check_add_no_overflow(idx1.extract(bs - 2, 0), arg1.extract(bs - 2, 0))) {
                            addressingMode::sbit_struct ss0 = addressingMode::_check_is_extract(idx1, bs - 1);
                            addressingMode::sbit_struct ss1 = addressingMode::_check_is_extract(arg1, bs - 1);
                            bool b0 = (ss0.sym_ast) ? true : ss0.rbit;
                            bool b1 = (ss1.sym_ast) ? true : ss1.rbit;
                            if ((!b0)||(!b1)) {
                                base = sext(arg1, extn);
                                return sext(idx1, extn);
                            }
                        }
                        goto goFaild;
                    }
                    else {
                        base = sext(arg1, extn);
                        return expr(c);
                    }
                }
                else {
                    base = expr(c);
                    if ((Z3_ast)idx1) {
                        return sext(idx1, extn);
                    }
                    else {
                        goto goFaild;
                    }
                }
            }

            case Z3_OP_ZERO_EXT: {
                uint64_t extn = Z3_get_decl_int_parameter(c, f, 0);
                expr arg1(c);
                expr idx1 = _ast2base(arg1, e.arg(0), deep + 1, max_deep);
                if ((Z3_ast)arg1) {
                    if ((Z3_ast)idx1) {
                        if (_check_add_no_overflow(idx1, arg1)) {
                            base = zext(arg1, extn);
                            return zext(idx1, extn);
                        }
                        goto goFaild;
                    }
                    else {
                        base = zext(arg1, extn);
                        return expr(c);
                    }
                }
                else {
                    base = expr(c);
                    if ((Z3_ast)idx1) {
                        return zext(idx1, extn);
                    }
                    else {
                        goto goFaild;
                    }
                }
            }
            case Z3_OP_EXTRACT: {
                UInt lo = e.lo();
                UInt hi = e.hi();
                expr arg1(c);
                expr idx1 = _ast2base(arg1, e.arg(0), deep + 1, max_deep);
                if ((Z3_ast)arg1) {
                    base = arg1.extract(hi, lo);
                }
                else {
                    base = expr(c);
                }
                if ((Z3_ast)idx1) {
                    return idx1.extract(hi, lo);
                }
                else {
                    return expr(c);
                }
            }
            case Z3_OP_CONCAT: {
                expr idx_sum(c);
                auto max = e.num_args();
                for (UInt i = 0; i < max; i++) {
                    expr arg1(c);
                    expr idx = _ast2base(arg1, e.arg(i), deep + 1, max_deep);
                    UInt LL = ((Z3_ast)arg1) ? arg1.get_sort().bv_size() : idx.get_sort().bv_size();
                    if (i != 0) {
                        if ((Z3_ast)idx && (Z3_ast)arg1) {
                            goto goFaild;
                        }
                    }

                    if ((Z3_ast)idx) {
                        if ((Z3_ast)idx_sum) {
                            idx_sum = concat(idx_sum, idx);
                        }
                        else {
                            idx_sum = idx;
                        }
                    }
                    else {
                        if ((Z3_ast)idx_sum) {
                            idx_sum = concat(idx_sum, c.bv_val(0, LL));
                        }
                        else {
                            idx_sum = c.bv_val(0, LL);
                        }
                    }

                    if ((Z3_ast)arg1) {
                        if ((Z3_ast)base) {
                            base = concat(base, arg1);
                        }
                        else {
                            base = arg1;
                        }
                    }
                    else {
                        if ((Z3_ast)base) {
                            base = concat(base, c.bv_val(0, LL));
                        }
                        else {
                            base = c.bv_val(0, LL);
                        }
                    }
                }

                return idx_sum;
            }
            default:
                break;
            }
        }
        else if (e.is_quantifier()) {
        }
        else if (e.is_numeral()) {
            base = e;
            return expr(c);
        }
        else {
        }
    }
goFaild:
    base = expr(c);;
    return e;
}


template<typename ADDR>
addressingMode<ADDR>::sbit_struct addressingMode<ADDR>::_check_is_extract(expr const& _e, UInt _idx) {
    context& c = _e.ctx();
    UInt idx = _idx;
    expr e = _e;
    //std::cout << e;
    while (True) {
        sort so = e.get_sort();
        UInt size = so.bv_size();
        if (e.kind() == Z3_APP_AST) {
            func_decl f = e.decl();
            switch (f.decl_kind())
            {
            case Z3_OP_SIGN_EXT: {
                uint64_t extn = Z3_get_decl_int_parameter(c, f, 0);
                e = e.arg(0);
                if (idx >= (size - extn)) {
                    idx = (size - extn) - 1;
                }
                break;
            }

            case Z3_OP_ZERO_EXT: {
                uint64_t extn = Z3_get_decl_int_parameter(c, f, 0);
                if (idx >= (size - extn)) {
                    return sbit_struct{ NULL, false, 0 };
                }
                else {
                    e = e.arg(0);
                }
                break;
            }

            case Z3_OP_EXTRACT: {
                UInt lo = e.lo();
                UInt hi = e.hi();
                e = e.arg(0);
                idx = idx + lo;
                break;
            }

            case Z3_OP_BSHL: {
                ULong shift;
                if (e.arg(1).simplify().is_numeral_u64(shift)) {
                    if (idx < shift) {
                        return sbit_struct{ NULL, false, 0 };
                    }
                    else {
                        e = e.arg(0);
                        idx = idx - shift;
                    }
                    break;
                }
                goto ret;
            }
            case Z3_OP_BLSHR: {
                ULong shift;
                if (e.arg(1).simplify().is_numeral_u64(shift)) {
                    if ((size - idx) <= shift) {
                        return sbit_struct{ NULL, false, 0 };
                    }
                    else {
                        e = e.arg(0);
                        idx = idx + shift;
                    }
                    break;
                }
                goto ret;
            }
            case Z3_OP_BASHR: {
                ULong shift;
                if (e.arg(1).simplify().is_numeral_u64(shift)) {
                    e = e.arg(0);
                    if ((size - idx) <= shift) {
                        idx = size - 1;
                    }
                    else {
                        idx = idx + shift;
                    }
                    break;
                }
                goto ret;
            }
            case Z3_OP_CONCAT: {
                auto max = e.num_args();
                UInt shift = 0;

                for (Int i = max - 1; i >= 0; i--) {
                    z3::expr arg = e.arg(i);
                    z3::sort arg_s = arg.get_sort();
                    UInt arg_s_l = arg_s.bv_size();
                    if (idx >= shift && idx < (arg_s_l + shift)) {
                        e = arg;
                        idx = idx - shift;
                        break;
                    }
                    shift += arg_s_l;
                }
                break;
            }
            case Z3_OP_BXOR: {
                auto max = e.num_args();
                UInt n_sym = 0;
                sbit_struct rSS;
                bool rb = false;
                for (Int i = max - 1; i >= 0; i--) {
                    z3::expr arg = e.arg(i);
                    sbit_struct SS = _check_is_extract(arg, idx);
                    if (SS.sym_ast) {
                        n_sym += 1;
                        rSS = SS;
                        if (n_sym == 2) goto ret;
                    }
                    else {
                        rb ^= SS.rbit;
                    }
                }
                return n_sym ? rSS : sbit_struct{ NULL, rb , 0 };
            }
            case Z3_OP_BAND: {
                auto max = e.num_args();
                UInt n_sym = 0;
                sbit_struct rSS;
                for (Int i = max - 1; i >= 0; i--) {
                    z3::expr arg = e.arg(i);
                    sbit_struct SS = _check_is_extract(arg, idx);
                    if (SS.sym_ast) {
                        n_sym += 1;
                        rSS = SS;
                    }
                    else {
                        if (!SS.rbit) 
                            return sbit_struct{ NULL, false , 0 };
                    }
                }
                if (n_sym == 1) 
                    return rSS;
                if (n_sym == 0)
                    return sbit_struct{ NULL, true , 0 };
                goto ret;
            }

            case Z3_OP_BOR: {
                auto max = e.num_args();
                UInt n_sym = 0;
                sbit_struct rSS;
                for (Int i = max - 1; i >= 0; i--) {
                    z3::expr arg = e.arg(i);
                    sbit_struct SS = _check_is_extract(arg, idx);
                    if (SS.sym_ast) {
                        n_sym += 1;
                        rSS = SS;
                    }
                    else {
                        if (SS.rbit)
                            return sbit_struct{ NULL, true , 0 };
                    }
                }
                if (n_sym == 1)
                    return rSS;
                if (n_sym == 0)
                    return sbit_struct{ NULL, false , 0 };
                goto ret;
            }
            default:
                goto ret;
            };
        }
        else if (e.kind() == Z3_NUMERAL_AST) {
            ULong real;
            e.is_numeral_u64(real);
            return sbit_struct{ NULL, (bool)((real >> idx) & 1), 0 };
        }
        else {
            break;
        }
    }
ret:
    return sbit_struct{ e, false, idx };
}




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

static inline Int newDifUser()
{
    std::unique_lock<std::mutex> lock(global_user_mutex);
    auto re = global_user++;
    return re;
}


template<typename ADDR>
MEM<ADDR>::MEM(solver& so, TRcontext& ctx, Bool _need_record) :
    m_solver(so),
    m_ctx(ctx),
    need_record(_need_record),
    user(newDifUser())
{
}

template<typename ADDR>
MEM<ADDR>::MEM(solver& so, TRcontext& ctx, MEM& father_mem, Bool _need_record) :
    m_solver(so),
    m_ctx(ctx),
    need_record(_need_record),
    user(newDifUser())
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


template void MEM<Addr32>::CheckSelf(PAGE*& P, Addr32 address);
template void MEM<Addr64>::CheckSelf(PAGE*& P, Addr64 address);
template void addressingMode<Addr32>::_offset2opAdd(std::vector<Vns>& ret, expr const& _e);
template void addressingMode<Addr64>::_offset2opAdd(std::vector<Vns>& ret, expr const& _e);
template bool addressingMode<Addr32>::_check_add_no_overflow(expr const& e1, expr const& e2);
template bool addressingMode<Addr64>::_check_add_no_overflow(expr const& e1, expr const& e2);
template expr addressingMode<Addr32>::_ast2base(expr& base, expr const& e, UInt deep, UInt max_deep);
template expr addressingMode<Addr64>::_ast2base(expr& base, expr const& e, UInt deep, UInt max_deep);
template addressingMode<Addr32>::sbit_struct addressingMode<Addr32>::_check_is_extract(expr const& _e, UInt _idx);
template addressingMode<Addr64>::sbit_struct addressingMode<Addr64>::_check_is_extract(expr const& _e, UInt _idx);
template MEM<Addr32>::MEM(solver& so, TRcontext& ctx, Bool _need_record);
template MEM<Addr64>::MEM(solver& so, TRcontext& ctx, Bool _need_record);
template MEM<Addr32>::MEM(solver& so, TRcontext& ctx, MEM& father_mem, Bool _need_record);
template MEM<Addr64>::MEM(solver& so, TRcontext& ctx, MEM& father_mem, Bool _need_record);
template MEM<Addr32>::~MEM();
template MEM<Addr64>::~MEM();
template Vns MEM<Addr32>::Iex_Load(Addr32 address, IRType ty);
template Vns MEM<Addr64>::Iex_Load(Addr64 address, IRType ty);
template Vns MEM<Addr32>::Iex_Load(Z3_ast address, IRType ty);
template Vns MEM<Addr64>::Iex_Load(Z3_ast address, IRType ty);
template void MEM<Addr32>::init_page(PAGE*& P, Addr32 address);
template void MEM<Addr64>::init_page(PAGE*& P, Addr64 address);
template UInt MEM<Addr32>::write_bytes(ULong address, ULong length, UChar* data);
template UInt MEM<Addr64>::write_bytes(ULong address, ULong length, UChar* data);
template void MEM<Addr32>::clearRecord();
template void MEM<Addr64>::clearRecord();
template ULong MEM<Addr32>::find_block_forward(ULong start, Addr32 size);
template ULong MEM<Addr64>::find_block_forward(ULong start, Addr64 size);
template ULong MEM<Addr32>::find_block_reverse(ULong start, Addr32 size);
template ULong MEM<Addr64>::find_block_reverse(ULong start, Addr64 size);
