#include "engine/mem_map.h"
#include "engine/memory.h"
using namespace TR;
template<class ST>



#define GETPT(address) ((*CR3)->pt[(address) >> 39 & 0x1ff]->pt[(address) >> 30 & 0x1ff]->pt[(address) >> 21 & 0x1ff])
#define GETPAGE(address) ((*CR3)->pt[(address) >> 39 & 0x1ff]->pt[(address) >> 30 & 0x1ff]->pt[(address) >> 21 & 0x1ff]->pt[(address) >> 12 & 0x1ff])
#define COPY_SYM(new_page, p_page,index) (new_page)->unit[(index)] = (p_page)->unit[(index)]


#define LCODEDEF1(PML4T_max,PML4T_ind,pdpt,PDPT_max,PDT,EXPRESS)															\
	if ((EXPRESS)) {																										\
			(*(pdpt))->pt = (PDT**)malloc(((PDPT_max) + 1) * sizeof(void *));												\
			memset((*(pdpt))->pt , 0, (PDPT_max + 1) * sizeof(void *));														\
			(*(pdpt))->size = (PDPT_max)+1;																					\
	}else {																													\
		(*(pdpt))->pt = (PDT**)malloc( 0x200 * sizeof(void *));																\
		memset((*(pdpt))->pt, 0, 0x200 * sizeof(void *));																	\
		(*(pdpt))->size = 0x200;																							\
	}

#define LCODEDEF2(PML4T_max, PML4T_ind, pdpt, PDPT_max, PDPT_ind, CR3 ,PDPT , PDT, EXPRESS)									\
	PDPT **pdpt = (*CR3)->pt + PML4T_ind;																					\
	if (!*pdpt) {																											\
		*pdpt = new PDPT;																									\
		if (!*pdpt)																											\
			goto _returnaddr;																								\
		memset(*pdpt, 0, sizeof(PDPT));																						\
		LCODEDEF1(PML4T_max,PML4T_ind,pdpt,PDPT_max,PDT,EXPRESS)															\
		(*CR3)->used += 1;																									\
		PDPT *orignal = (*CR3)->top;																						\
		(*CR3)->top = *pdpt;																								\
		(*pdpt)->prev = NULL;																								\
		(*pdpt)->next = orignal;																							\
		(*pdpt)->index = PML4T_ind;																							\
		if (orignal) orignal->prev = *pdpt;																					\
	}																														\
	else if ((*pdpt)->size <= PDPT_ind) {																					\
		if (PML4T_max == PML4T_ind) {																						\
			(*pdpt)->pt = (PDT**)realloc((*pdpt)->pt, (PDPT_ind + 1) * sizeof(void *));										\
			memset((*pdpt)->pt + (*pdpt)->size, 0, (PDPT_ind + 1 - (*pdpt)->size) * sizeof(void *));						\
			(*pdpt)->size = PDPT_ind + 1;																					\
		}																													\
		else {																												\
			(*pdpt)->pt = (PDT**)realloc((*pdpt)->pt,0x200*sizeof(void *));													\
			memset((*pdpt)->pt + (*pdpt)->size, 0, (0x200 - (*pdpt)->size) * sizeof(void *));								\
			(*pdpt)->size = 0x200;																							\
		}																													\
	}

#define LCODEDEF3(page,PT,pt)																								\
delete *page;																												\
*page = 0;																													\
(*pt)->used -= 1;																											\
if ((*pt)->used) {																											\
	address += 0x1000;																										\
	continue;																												\
}																															\
{																															\
	PT *p = (*pt)->prev;																									\
	PT *n = (*pt)->next;																									\
	if (p) p->next = n;																										\
	if (n) n->prev = p;																										\
}																														  

#define LCODEDEF4(PDPT,pdpt_point,CR3_point,lCR3,pdpt,i1)																	\
PDPT *pdpt_point = CR3_point->top;																							\
for (UInt i1 = 0; i1 < CR3_point->used; i1++, pdpt_point = pdpt_point->next) {												\
	PDPT *pdpt = new PDPT;																									\
	memset(pdpt, 0, sizeof(PDPT));																							\
	if (!lCR3->pt) {																										\
		lCR3->pt = (PDPT**)malloc(CR3_point->size * 8);																		\
		memset(lCR3->pt,0,CR3_point->size * 8);																				\
	}																														\
	lCR3->pt[pdpt_point->index] = pdpt;																						\
	{																														\
		PDPT *orignal = lCR3->top;																							\
		lCR3->top = pdpt;																									\
		(pdpt)->prev = NULL;																								\
		(pdpt)->next = orignal;																								\
		(pdpt)->index = pdpt_point->index;																					\
		if (orignal) orignal->prev = pdpt;																					\
	}																														\


#define LCODEDEF5(PDPT,pdpt_point,free_pdpt_point,CR3_point,i1,codenext)													\
PDPT *pdpt_point = CR3_point->top;																							\
for (UInt i1 = 0; i1 < CR3_point->used; i1++) {																				\
	codenext																												\
	free(pdpt_point->pt);																									\
	auto free_pdpt_point = pdpt_point;																						\
	pdpt_point = pdpt_point->next;																							\
	delete free_pdpt_point;																									\
}                                                                                                                           \



#define LMAX1 PML4T_max
#define LMAX2 PDPT_max
#define LMAX3 PDT_max
#define LMAX4 PT_max
#define LMAX5 PAGE_max

#define LIND1 PML4T_ind
#define LIND2 PDPT_ind
#define LIND3 PDT_ind
#define LIND4 PT_ind

#define LTAB1 CR3
#define LTAB2 pdpt
#define LTAB3 pdt
#define LTAB4 pt
#define LTAB5 page

#define LSTRUCT1 PML4T
#define LSTRUCT2 PDPT
#define LSTRUCT3 PDT
#define LSTRUCT4 PT
#define LSTRUCT5 ST


ULong mapping<ST>::map(ULong address, ULong length){
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
                    (*CR3)->pt = (PDPT**)malloc((PML4T_max + 1) * 8);
                    memset((*CR3)->pt, 0, (PML4T_max + 1) * sizeof(void*));
                    (*CR3)->size = PML4T_max + 1;
                }
                else {
                    if ((*CR3)->size <= PML4T_max) {
                        (*CR3)->pt = (PDPT**)realloc((*CR3)->pt, (PML4T_ind + 1) * sizeof(void*));
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

                ST** page = (*pt)->pt + PT_ind;
                if (!*page) {
                    *page = map_interface(address);
                    //Over
                    PAGE_link* page_l = new PAGE_link;
                    if (!*page)
                        goto _returnaddr;
                    (*pt)->used += 1;
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
                if (address == 0) return -1ull;
            }
            return 0;
        _returnaddr:
            return max - address + 0x1000;
        }

template<class ST>
void TR::mapping<ST>::copy(PML4T* cr3)
 {
    PML4T* CR3_point = cr3;
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
                    copy_interface(&pt->pt[index], &pt_point->pt[index]);
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


template<class ST>
ULong TR::mapping<ST>::unmap(ULong address, ULong length)
{
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
        ST** page = (*pt)->pt + PT_ind;
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
            unmap_interface(page);
            // LCODEDEF3(LTAB5, LSTRUCT4, LTAB4)
            (*pt)->used -= 1;
            if ((*pt)->used) {
                address += 0x1000;
                continue;
            }
            {
                PT* p = (*pt)->prev;
                PT* n = (*pt)->next;
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

template<class ST>
void TR::mapping<ST>::recycle()
 {
    if (!CR3[0]) return;
    PML4T* CR3_point = CR3[0];
    //  ±éÀúË«ÏòÁ´±í
    LCODEDEF5(LSTRUCT2, pdpt_point, free_pdpt_point, CR3_point, i1,
        LCODEDEF5(LSTRUCT3, pdt_point, free_pdt_point, pdpt_point, i2,
            LCODEDEF5(LSTRUCT4, pt_point, free_pt_point, pdt_point, i3,
                PAGE_link * page_point = pt_point->top;
                for (UInt i4 = 0; i4 < pt_point->used; i4++) {
                    UShort index = page_point->index;
                    unmap_interface(&pt_point->pt[index]);
                    auto free_page_point = page_point;
                    page_point = page_point->next;
                    delete free_page_point;
                }
            )
        )
    )
    CR3[0] = nullptr;
}



template TR::mapping<PAGE>;