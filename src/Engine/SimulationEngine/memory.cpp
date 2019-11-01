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
#define vpanic(...) printf("%s line %d",__FILE__,__LINE__); vpanic(__VA_ARGS__);

unsigned int    global_user;
std::mutex      global_user_mutex;

using namespace z3;

// 自实现的(不确定是否正确) 
// 解析ast表达式: ast(symbolic address) = numreal(base) + symbolic(offset) 用于cpu符号内存寻址
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


addressingMode::sbit_struct addressingMode::check_is_extract(expr const& _e, UInt _idx) {
    context& c = _e.ctx();
    UInt idx = _idx;
    expr e = _e;
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
                if (e.arg(1).is_numeral_u64(shift)) {
                    if (idx < shift) {
                        return sbit_struct{ NULL, false, 0 };
                    }
                    else {
                        e = e.arg(0);
                        idx = idx - shift;
                    }
                }
                break;
            }
            case Z3_OP_BLSHR: {
                ULong shift;
                if (e.arg(1).is_numeral_u64(shift)) {
                    if ((size - idx) <= shift) {
                        return sbit_struct{ NULL, false, 0 };
                    }
                    else {
                        e = e.arg(0);
                        idx = idx + shift;
                    }
                }
                break;
            }
            case Z3_OP_BASHR: {
                ULong shift;
                if (e.arg(1).is_numeral_u64(shift)) {
                    e = e.arg(0);
                    if ((size - idx) <= shift) {
                        idx = size - 1;
                    }
                    else {
                        idx = idx + shift;
                    }
                }
                break;
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
            default:
                goto ret;
            };
        }
        else if (e.kind() == Z3_NUMERAL_AST) {
            ULong real;
            e.is_numeral_u64(real);
            return sbit_struct{ NULL, (bool)(real >> idx), 0 };
        }
        else {
            break;
        }
    }
ret:
    return sbit_struct{ e, false, idx };
}





static inline UInt newDifUser()
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
        vpanic("error inc_used_ref ???");
    }
    pt->used_point++;
    pt->unit_mutex = true;
}


static inline int dec_used_ref(PAGE *pt) {
    bool xchgbv = false;
    while (!xchgbv) {
        __asm__ __volatile("xchgb %b0,%1":"=r"(xchgbv) : "m"(pt->unit_mutex), "0"(xchgbv) : "memory");
    }
    if (--pt->used_point) {
        pt->unit_mutex = true;
        return True;
    }else{
        if (pt->unit)
            delete pt->unit;
        delete pt;
        return False;
    }
}

MEM::MEM(State& so, context* ctx, Bool _need_record) :
    m_state(so),
    m_ctx(*ctx),
    need_record(_need_record)
{
    this->CR3 = (PML4T * *)malloc(8);
    *(this->CR3) = new PML4T;
    memset(*(this->CR3), 0, sizeof(PML4T));
    this->user = newDifUser();
}

MEM::MEM(State& so, MEM& father_mem, context* ctx, Bool _need_record) :
    m_state(so),
    m_ctx(*ctx),
    need_record(_need_record)
{
    this->CR3 = (PML4T * *)malloc(8);
    *(this->CR3) = new PML4T;
    memset(*(this->CR3), 0, sizeof(PML4T));
    this->user = newDifUser();
    vassert(this->user != father_mem.user);
    this->copy(father_mem);
}

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
                    dec_used_ref(pt);

                    auto free_page_point = page_point;
                    page_point = page_point->next;
                    delete free_page_point;
                }
            )
        )
    )
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
            (*page)->user = -1ull;
            (*page)->unit = NULL;
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
                        pt->pt[index] = pt_point->pt[index];//copy
                        //(pt->pt[index])->used_point += 1;
                        inc_used_ref((pt->pt[index]));
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
                LCODEDEF3(LTAB5, LSTRUCT4, LTAB4)
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
    };

    //very fast
    void MEM::write_bytes(ULong address, ULong length, UChar* data) {
        if (length < 8) {
            {
                ULong max = address + length;
                PAGE* p_page = GETPAGE(address);
                if (!p_page->unit) {
                    p_page->unit = new Register<0x1000>(m_ctx, need_record);
                    p_page->user = user;
                }
                UInt count = 0;
                while (address < max) {
                    if (!(address % 0x1000)) {
                        p_page = GETPAGE(address);
                        if (!p_page->unit) {
                            p_page->unit = new Register<0x1000>(m_ctx, need_record);
                            p_page->user = user;
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
            PAGE* p_page = GETPAGE(address);
            if ((((ULong*)data)[0] & (~(-1ull << (align_l << 3)))) || p_page->unit){
                if (!p_page->unit) {
                    p_page->unit = new Register<0x1000>(m_ctx, need_record);
                    p_page->user = user;
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
                p_page = GETPAGE(address + count);
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
                    if (!need_mem) {
                        count = ALIGN(address + count + 0x1000, 0x1000) - address;
                        continue;
                    }
                    else {
                        p_page->unit = new Register<0x1000>(m_ctx, need_record);
                        p_page->user = user;
                    }
                }
            }
            *(ULong*)(&p_page->unit->m_bytes[(address + count) & 0xfff]) = *(ULong*)(data + count);
            count += 8;
        };
        if (align_r) {
            if ((!((address + count) & 0xfff))||!p_page) {
                p_page = GETPAGE(address + count);
            }
            if (((*(ULong*)(data + count)) & ((1ull << (align_r << 3)) - 1)) || need_mem || p_page->unit) {
                if (!p_page->unit) {
                    p_page->unit = new Register<0x1000>(m_ctx, need_record);
                    p_page->user = user;
                }
                memcpy(&p_page->unit->m_bytes[(address + count) & 0xfff], &data[count], align_r);
            }
        }
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
        default:vpanic("2333333");
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
            vpanic("2333333");
        }
    }

    void MEM::CheckSelf(PAGE*& P, ADDR address)
    {
        if (user != P->user) {//WNC
            if (P->user == -1ull) {
                bool xchgbv = false;
                while (!xchgbv) {
                    __asm__ __volatile("xchgb %b0,%1":"=r"(xchgbv) : "m"(P->unit_mutex), "0"(xchgbv) : "memory");
                }
                vassert(P->unit == NULL);
                P->unit = new Register<0x1000>(m_ctx, need_record);
                P->user = user;
                memset(P->unit->m_bytes, 0, 0x1000);
                mem_change_map[ALIGN(address, 0x1000)] = P->unit;
                P->unit_mutex = True;
                return;
            }
            Addr64 e_address = address;
            PT* pt = GETPT(e_address);
            auto ptindex = (e_address >> 12 & 0x1ff);
            PAGE** page = pt->pt + ptindex;
            PAGE_link* pl = pt->top;
            *page = new PAGE;
            (*page)->unit = new Register<0x1000>(*(P->unit), m_ctx, need_record);

            //--P->used_point;
            dec_used_ref(P);
            P = (*page);
            P->user = user;
            P->used_point = 1;
            P->unit_mutex = true;
            mem_change_map[ALIGN(address, 0x1000)] = (*page)->unit;
        }
    }

