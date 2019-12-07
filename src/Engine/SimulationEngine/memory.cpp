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
#include "State_class.hpp"

unsigned int    global_user;
std::mutex      global_user_mutex;

using namespace z3;

//a=b+c+d+e...+z -> b c d e
void addressingMode::_offset2opAdd(std::vector<Vns> &ret, expr const& _e)
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

bool addressingMode::_check_add_no_overflow(expr const& e1, expr const& e2) {
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
expr addressingMode::_ast2base(expr& base,
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


addressingMode::sbit_struct addressingMode::_check_is_extract(expr const& _e, UInt _idx) {
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





static inline Int newDifUser()
{
    std::unique_lock<std::mutex> lock(global_user_mutex);
    auto re = global_user++;
    return re;
}

static inline void inc_used_ref(PAGE *pt) {
    bool xchgbv = false;
    while (!xchgbv) {
        __asm__ __volatile("xchgb %b0,%1":"=r"(xchgbv) : "m"(pt->unit_mutex), "0"(xchgbv) : "memory");
    }
    if (!pt->used_point) {
        VPANIC("error inc_used_ref ???");
    }
    pt->used_point++;
    pt->unit_mutex = true;
}


static inline int dec_used_ref(PAGE *pt) {
    bool xchgbv = false;
    while (!xchgbv) {
        __asm__ __volatile("xchgb %b0,%1":"=r"(xchgbv) : "m"(pt->unit_mutex), "0"(xchgbv) : "memory");
    }
    if (!pt->used_point) {
        VPANIC("error dec_used_ref ???");
    }
    if (--pt->used_point) {
        pt->unit_mutex = true;
        return True;
    }else{
        pt->unit_mutex = true;
        return False;
    }
}

MEM::MEM(State& so, TRcontext& ctx, Bool _need_record) :
    m_state(so),
    m_ctx(ctx),
    need_record(_need_record)
{
    this->CR3 = (PML4T * *)malloc(8);
    *(this->CR3) = new PML4T;
    memset(*(this->CR3), 0, sizeof(PML4T));
    this->user = newDifUser();
}

MEM::MEM(State& so, MEM& father_mem, TRcontext& ctx, Bool _need_record) :
    m_state(so),
    m_ctx(ctx),
    need_record(_need_record)
{
    this->CR3 = (PML4T * *)malloc(8);
    *(this->CR3) = new PML4T;
    memset(*(this->CR3), 0, sizeof(PML4T));
    this->user = newDifUser();
    vassert(this->user != father_mem.user);
    this->copy(father_mem);
}

ULong MEM::map(ULong address, ULong length) {
    ULong max = (address + length - 1) & (~0xfff);
    UShort PML4T_max = (max >> 39 & 0x1ff);
    UShort PDPT_max = (max >> 30 & 0x1ff);
    UShort PDT_max = (max >> 21 & 0x1ff);
    UShort PT_max = (max >> 12 & 0x1ff);
    address &= (~0xfff);
    while (address <= max) {
        UShort PML4T_ind = (address >> 39 & 0x1ff);
        UShort PDPT_ind = (address >> 30 & 0x1ff);
        UShort PDT_ind = (address >> 21 & 0x1ff);
        UShort PT_ind = (address >> 12 & 0x1ff);
        if (!(*CR3)->pt) {
            (*CR3)->pt = (PDPT * *)malloc((PML4T_max + 1) * 8);
            memset((*CR3)->pt, 0, (PML4T_max + 1) * sizeof(void*));
            (*CR3)->size = PML4T_max + 1;
        }
        else {
            if ((*CR3)->size <= PML4T_max) {
                (*CR3)->pt = (PDPT * *)realloc((*CR3)->pt, (PML4T_ind + 1) * sizeof(void*));
                memset((*CR3)->pt + (*CR3)->size, 0, (PML4T_ind + 1 - (*CR3)->size) * sizeof(void*));
                (*CR3)->size = PML4T_ind + 1;
            }
        }

        LCODEDEF2(LMAX1, LIND1, LTAB2, LMAX2, LIND2, LTAB1, LSTRUCT2, LSTRUCT3, (LMAX1) == (LIND1));
        LCODEDEF2(LMAX2, LIND2, LTAB3, LMAX3, LIND3, LTAB2, LSTRUCT3, LSTRUCT4, (LMAX1) == (LIND1) && (LMAX2) == (LIND2));
        LCODEDEF2(LMAX3, LIND3, LTAB4, LMAX4, LIND4, LTAB3, LSTRUCT4, LSTRUCT5, (LMAX1) == (LIND1) && (LMAX2) == (LIND2) && (LMAX3) == (LIND3));
        /* debug LCODEDEF2(LMAX1, LIND1, .... )
        PT **pt = (*pdt)->pt + PDT_ind;
        if (!*pt) {
            *pt = new PT;
            if (!*pt) goto _returnaddr; memset(*pt, 0, sizeof(PT));
            if (((PML4T_max) == (PML4T_ind) && (PDPT_max) == (PDPT_ind) && (PDT_max) == (PDT_ind))) {
                (*(pt))->pt = (PAGE**)malloc(((PT_max)+1) * sizeof(void *)); memset((*(pt))->pt, 0, (PT_max + 1) * sizeof(void *)); (*(pt))->size = (PT_max)+1;
            } else {
                (*(pt))->pt = (PAGE**)malloc(0x200 * sizeof(void *)); memset((*(pt))->pt, 0, 0x200 * sizeof(void *)); (*(pt))->size = 0x200;
            }
            (*pdt)->used += 1;
            PT *orignal = (*pdt)->top;
            (*pdt)->top = *pt; (*pt)->prev = 0;
            (*pt)->next = orignal;
            (*pt)->index = PDT_ind;
            if (orignal) orignal->prev = *pt;
        }
        else if ((*pt)->size <= PDPT_ind) {
            if (PDT_max == PDT_ind) {
                (*pt)->pt = (PAGE**)realloc((*pt)->pt, (PDPT_ind + 1) * sizeof(void *));
                memset((*pt)->pt + (*pt)->size, 0, (PDPT_ind + 1 - (*pt)->size) * sizeof(void *));
                (*pt)->size = PDPT_ind + 1;
            } else {
                (*pt)->pt = (PAGE**)realloc((*pt)->pt, 0x200 * sizeof(void *));
                memset((*pt)->pt + (*pt)->size, 0, (0x200 - (*pt)->size) * sizeof(void *)); (*pt)->size = 0x200;
            }
        };*/

        PAGE** page = (*pt)->pt + PT_ind;
        if (!*page) {
            //
            *page = new PAGE;
            PAGE_link* page_l = new PAGE_link;
            if (!*page)
                goto _returnaddr;
            memset(*page, 0, sizeof(PAGE));
            (*pt)->used += 1;
            (*page)->unit_mutex = true;
            (*page)->used_point = 1;
            (*page)->user = user;
            (*page)->unit = NULL;
            (*page)->is_pad = false;
            //Over

            PAGE_link* orignal = (*pt)->top;
            (*pt)->top = page_l;
            (page_l)->prev = NULL;
            (page_l)->next = orignal;
            (page_l)->index = PT_ind;
            if (orignal) orignal->prev = page_l;
        }
        else {
            //goto _returnaddr; 
        }
        address += 0x1000;
    }
    return 0;
_returnaddr:
    return max - address + 0x1000;
}



void MEM::copy(MEM& mem) {
    PML4T* CR3_point = *(mem.CR3);
    PML4T* lCR3 = *CR3;
    LCODEDEF4(LSTRUCT2, pdpt_point, CR3_point, lCR3, LTAB2, i1);
        LCODEDEF4(LSTRUCT3, pdt_point, pdpt_point, LTAB2, LTAB3, i2);
            LCODEDEF4(LSTRUCT4, pt_point, pdt_point, LTAB3, LTAB4, i3);
                PAGE_link* page_point = pt_point->top;
                for (UInt i4 = 0; i4 < pt_point->used; i4++, page_point = page_point->next) {
                    UShort index = page_point->index;
                    PAGE_link* page_l = new PAGE_link;
                    memset(page_l, 0, sizeof(PAGE_link));
                    if (!pt->pt) {
                        pt->pt = (PAGE * *)malloc(pt_point->size * 8);
                        memset(pt->pt, 0, pt_point->size * 8);
                    }
#ifndef CLOSECNW
#ifdef USECNWNOAST
                    PAGE* fpage = pt_point->pt[index];
                    if (!fpage->is_pad) {
                        if (fpage->unit->symbolic) {
                            PAGE* page = new PAGE;
                            pt->pt[index] = page;
                            page->unit_mutex = true;
                            page->used_point = 1;
                            page->user = user;
                            page->unit = new Register<0x1000>(*(fpage->unit), m_ctx, need_record);
                            page->is_pad = false;
                            goto dont_use_father_page;
                        }
                    }
                    pt->pt[index] = pt_point->pt[index];//copy
                    inc_used_ref((pt->pt[index]));
                    dont_use_father_page:
#else
                    pt->pt[index] = pt_point->pt[index];//copy
                    inc_used_ref((pt->pt[index]));
#endif
#else
                    PAGE* fpage = pt_point->pt[index];
                    PAGE *page = new PAGE;
                    pt->pt[index] = page;
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
                    {
                        PAGE_link* orignal = (pt)->top;
                        pt->top = page_l;
                        (page_l)->prev = NULL;
                        (page_l)->next = orignal;
                        (page_l)->index = index;
                        if (orignal) orignal->prev = page_l;
                    }
                }
                pt->used = pt_point->used;
                pt->size = pt_point->size;
            }
            pdt->used = pdt_point->used;
            pdt->size = pdt_point->size;
        }
        pdpt->used = pdpt_point->used;
        pdpt->size = pdpt_point->size;
    }
    lCR3->used = CR3_point->used;
    lCR3->size = CR3_point->size;
}

ULong MEM::unmap(ULong address, ULong length) {
    ULong max = (address + length - 1) & (~0xfff);
    address &= (~0xfff);
#ifdef OPSTR
    int freecount = 0;
#endif
    while (address <= max) {
        PDPT** pdpt = (*CR3)->pt + (address >> 39 & 0x1ff);
        if (!*pdpt) {
            return address;
        }
        PDT** pdt = (*pdpt)->pt + (address >> 30 & 0x1ff);
        if (!*pdt) {
            return address;
        }
        PT** pt = (*pdt)->pt + (address >> 21 & 0x1ff);
        if (!*pt) {
            return address;
        }
        UShort PT_ind = (address >> 12 & 0x1ff);
        PAGE** page = (*pt)->pt + PT_ind;
        if (*page) {
            PAGE_link* page_l = (*pt)->top;
            for (UInt i = 0; i < (*pt)->used; i++, page_l = page_l->next) {
                if ((page_l) && (page_l->index == PT_ind)) {
                    {
                        PAGE_link* p = (page_l)->prev;
                        PAGE_link* n = (page_l)->next;
                        if (p) p->next = n;
                        if (n) n->prev = p;
                    }
                    delete page_l;
#ifdef OPSTR
                    freecount++;
#endif
                    break;
                }
            }

            //need define
            if ((*page)->unit) {
                delete (*page)->unit;
            }
            delete *page;	

            // LCODEDEF3(LTAB5, LSTRUCT4, LTAB4)
            *page = 0;				
            (*pt)->used -= 1;		
            if ((*pt)->used) {		
	            address += 0x1000;	
	            continue;			
            }						
            {						
	            PT *p = (*pt)->prev;
	            PT *n = (*pt)->next;
	            if (p) p->next = n;	
	            if (n) n->prev = p;	
            }
            free((*pt)->pt);
            LCODEDEF3(LTAB4, LSTRUCT3, LTAB3)
            free((*pdt)->pt);
            LCODEDEF3(LTAB3, LSTRUCT2, LTAB2)
            free((*pdpt)->pt);
            delete* pdpt;
            *pdpt = 0;
            (*CR3)->used -= 1;
            address += 0x1000;
        }
        else {
            return address;
        }
    }
#ifdef OPSTR
    vex_printf("free count %x\n", freecount);
#endif
    return 0;
}
void MEM::clearRecord()
{
    for (auto p : mem_change_map) {
        p.second->clearRecord();
    }
    mem_change_map.clear();
}
;


MEM::~MEM() {
    PML4T* CR3_point = *CR3;
    //  遍历双向链表
    LCODEDEF5(LSTRUCT2, pdpt_point, free_pdpt_point, CR3_point, i1,
        LCODEDEF5(LSTRUCT3, pdt_point, free_pdt_point, pdpt_point, i2,
            LCODEDEF5(LSTRUCT4, pt_point, free_pt_point, pdt_point, i3,
                PAGE_link * page_point = pt_point->top;
                for (UInt i4 = 0; i4 < pt_point->used; i4++) {
                    UShort index = page_point->index;

                    PAGE* pt = pt_point->pt[index];
                    if (pt->user == user) {
                        vassert(pt->used_point == 1);
                        if (pt->unit) {
                            delete pt->unit;
                        }
                        delete pt;
                    }
                    else {
                        dec_used_ref(pt);
                    }
                    auto free_page_point = page_point;
                    page_point = page_point->next;
                    delete free_page_point;
                }
            )
        )
    )
        delete CR3_point;
    free(CR3);
}


    Vns MEM::Iex_Load(ADDR address, IRType ty)
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

    Vns MEM::Iex_Load(Z3_ast address, IRType ty) {
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

void MEM::CheckSelf(PAGE*& P, ADDR address)
{
#ifndef CLOSECNW
    if (user == P->user) {
#ifdef USECNWNOAST
        mem_change_map[ALIGN(address, 0x1000)] = P->unit;
#endif
        return; 
    }
    bool xchgbv = false;
    while (!xchgbv) { __asm__ __volatile("xchgb %b0,%1":"=r"(xchgbv) : "m"(P->unit_mutex), "0"(xchgbv) : "memory"); }
    PAGE** page = get_pointer_of_mem_page(address);
    if (user == (*page)->user) {
        P->unit_mutex = true;
        P = (*page);
        return;
    }
    //--P->used_point;
    vassert(P->used_point);
    --P->used_point;
    PAGE* np = new PAGE;
    if (P->is_pad) {// 该页是填充区，则开始分配该页
        vassert(P->unit == NULL);
        np->unit = new Register<0x1000>(m_ctx, need_record);
        memset(np->unit->m_bytes, P->pad, 0x1000);
    }
    else {
        np->unit = new Register<0x1000>(*(P->unit), m_ctx, need_record);
    }

    np->user = user;
    np->used_point = 1;
    np->is_pad = false;
    np->unit_mutex = true;
    *page = np;
    P->unit_mutex = true;
    P = np;
    mem_change_map[ALIGN(address, 0x1000)] = np->unit;
#else
    vassert(user == P->user);
    mem_change_map[ALIGN(address, 0x1000)] = P->unit;
#endif
}

void MEM::init_page(PAGE*& P, ADDR address)
{
    //WNC
    if (user == P->user) return;
    bool xchgbv = false;
    while (!xchgbv) { __asm__ __volatile("xchgb %b0,%1":"=r"(xchgbv) : "m"(P->unit_mutex), "0"(xchgbv) : "memory"); }
    PAGE** page = get_pointer_of_mem_page(address);
    if (user == (*page)->user) {
        P->unit_mutex = true;
        P = (*page);
        return;
    }
    vassert(P->used_point);
    --P->used_point;
    PAGE* np = new PAGE;
    np->unit = nullptr;
    np->user = user;
    np->used_point = 1;
    np->is_pad = false;
    np->unit_mutex = true;
    *page = np;
    P->unit_mutex = true;
    P = np;
    
}

//very fast
void MEM::write_bytes(ULong address, ULong length, UChar* data) {
    if (length < 8) {
        {
            ULong max = address + length;
            PAGE* p_page = getMemPage(address);
            MEMACCESSASSERT(p_page, address);
            init_page(p_page, address);
            if (!p_page->unit) {
                p_page->unit = new Register<0x1000>(m_ctx, need_record);
            }
            UInt count = 0;
            while (address < max) {
                if (!(address % 0x1000)) {
                    p_page = getMemPage(address);
                    MEMACCESSASSERT(p_page, address);
                    init_page(p_page, address);
                    if (!p_page->unit) {
                        p_page->unit = new Register<0x1000>(m_ctx, need_record);
                    }
                }
                p_page->unit->m_bytes[address & 0xfff] = data[count];
                address += 1;
                count += 1;
            };
            return;
        }
    }
    bool first_flag = false;
    UInt align_l = 8 - (address - ALIGN(address, 8));
    UInt align_r = (address + length - ALIGN(address + length, 8));
    if (align_l == 8) {
    }
    else {
        PAGE* p_page = getMemPage(address);
        MEMACCESSASSERT(p_page, address);
        init_page(p_page, address);
        if ((((ULong*)data)[0] & (~(-1ull << (align_l << 3)))) || p_page->unit) {
            if (!p_page->unit) {
                p_page->unit = new Register<0x1000>(m_ctx, need_record);
            }
            first_flag = true;
            memcpy(&p_page->unit->m_bytes[address & 0xfff], data, align_l);
        }
        data += align_l;
        address += align_l;
        length -= align_l;
    }
    UInt count = 0;
    ULong max = (ALIGN(address + length, 8) - address);
    PAGE* p_page = nullptr;

    bool need_mem = false;
    bool need_check = true;
    while (count < max) {
        if ((!((address + count) & 0xfff)) || (need_check)) {
            p_page = getMemPage(address + count);
            MEMACCESSASSERT(p_page, address + count);
            init_page(p_page, address + count);
            ULong smax = (count + 0x1000 <= max) ? 0x1000 : max - count;
            need_mem = false;
            if (!p_page->unit) {
                for (ADDR idx = 0; idx < smax; idx += 8) {
                    if (*(ULong*)(&data[count + idx])) {
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
                    p_page->unit = new Register<0x1000>(m_ctx, need_record);
                }
                else {
                    count = ALIGN(address + count + 0x1000, 0x1000) - address;
                    p_page->is_pad = True;
                    p_page->pad = 0;
                    continue;
                }
            }
        }
        *(ULong*)(&p_page->unit->m_bytes[(address + count) & 0xfff]) = *(ULong*)(data + count);
        count += 8;
    };
    if (align_r) {
        if ((!((address + count) & 0xfff)) || !p_page) {
            p_page = getMemPage(address + count);
            MEMACCESSASSERT(p_page, address + count);
            init_page(p_page, address + count);
        }
        if (((*(ULong*)(data + count)) & ((1ull << (align_r << 3)) - 1)) || need_mem || p_page->unit) {
            if (!p_page->unit) {
                p_page->unit = new Register<0x1000>(m_ctx, need_record);
            }
            memcpy(&p_page->unit->m_bytes[(address + count) & 0xfff], &data[count], align_r);
        }
        else {
            p_page->is_pad = True;
            p_page->pad = 0;
        }
    }
}