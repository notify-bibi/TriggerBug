#ifndef MEM_H
#define MEM_H

using namespace z3;
#include "memory_CD.hpp"

#define SYMBOLIC_TYPE _Z3_ast

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
}



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
#define LSTRUCT5 PAGE

static inline UInt newDifUser()
{
	std::unique_lock<std::mutex> lock(global_user_mutex);
	return global_user++;
}


MEM::MEM(solver *so, context * ctx, Bool _need_record) : m_solv(so), m_ctx(*ctx), need_record(_need_record) {
	this->CR3 = (PML4T**)malloc(8);
	*(this->CR3) = new PML4T;
	memset(*(this->CR3), 0, sizeof(PML4T));
	this->user = newDifUser();
}
MEM::MEM(solver *so,MEM &father_mem, context * ctx, Bool _need_record): m_solv(so), m_ctx(*ctx), need_record(_need_record) {
	this->CR3 = (PML4T**)malloc(8);
	*(this->CR3) = new PML4T;
	memset(*(this->CR3), 0, sizeof(PML4T));
	this->user = newDifUser();
	vassert(this->user != father_mem.user);
	this->copy(father_mem);
}
inline MEM::~MEM() {
	for (auto _Page : mem_change_map) {
		delete _Page.second;
	}
	freeMap();
}
inline void MEM::freeMap() {
	PML4T *CR3_point = *CR3;
	LCODEDEF5(LSTRUCT2, pdpt_point, free_pdpt_point, CR3_point, i1,
		LCODEDEF5(LSTRUCT3, pdt_point, free_pdt_point, pdpt_point, i2,
			LCODEDEF5(LSTRUCT4, pt_point, free_pt_point, pdt_point, i3,
				PAGE_link *page_point = pt_point->top;
	for (UInt i4 = 0; i4 < pt_point->used; i4++) {
		UShort index = page_point->index;
		
		/*PAGE * pt = pt_point->pt[index];
		if(pt->unit)
			delete pt->unit;
		delete pt;*/

		auto free_page_point = page_point;
		page_point = page_point->next;
		delete free_page_point;
	}
			)
		)
	)
}

ULong MEM::map(ULong address, ULong length) {
	ULong max = (address + length - 1)&(~0xfff);
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
			memset((*CR3)->pt, 0, (PML4T_max + 1) * sizeof(void *));
			(*CR3)->size = PML4T_max + 1;
		}
		else {
			if ((*CR3)->size <= PML4T_max) {
				(*CR3)->pt = (PDPT**)realloc((*CR3)->pt, (PML4T_ind + 1) * sizeof(void *));
				memset((*CR3)->pt + (*CR3)->size, 0, (PML4T_ind + 1 - (*CR3)->size) * sizeof(void *));
				(*CR3)->size = PML4T_ind + 1;
			}
		}

		LCODEDEF2(LMAX1, LIND1, LTAB2, LMAX2, LIND2, LTAB1, LSTRUCT2, LSTRUCT3, (LMAX1) == (LIND1));
		LCODEDEF2(LMAX2, LIND2, LTAB3, LMAX3, LIND3, LTAB2, LSTRUCT3, LSTRUCT4, (LMAX1) == (LIND1) && (LMAX2) == (LIND2));
		LCODEDEF2(LMAX3, LIND3, LTAB4, LMAX4, LIND4, LTAB3, LSTRUCT4, LSTRUCT5, (LMAX1) == (LIND1) && (LMAX2) == (LIND2) && (LMAX3) == (LIND3));
		/*PT **pt = (*pdt)->pt + PDT_ind;
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

		PAGE **page = (*pt)->pt + PT_ind;
		if (!*page) {
			//初始化
			*page = new PAGE;
			PAGE_link *page_l = new PAGE_link;
			if (!*page)
				goto _returnaddr;
			memset(*page, 0, sizeof(PAGE));
			(*pt)->used += 1;
			(*page)->used_point += 1;
			(*page)->user = -1ull;
			(*page)->unit = NULL;
			//初始化Over

			PAGE_link *orignal = (*pt)->top;
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
void MEM::copy(MEM &mem) {
	PML4T *CR3_point = *(mem.CR3);
	PML4T *lCR3 = *CR3;
	LCODEDEF4(LSTRUCT2, pdpt_point, CR3_point, lCR3, LTAB2, i1);
		LCODEDEF4(LSTRUCT3, pdt_point, pdpt_point, LTAB2, LTAB3, i2);
			LCODEDEF4(LSTRUCT4, pt_point, pdt_point, LTAB3, LTAB4, i3);
				PAGE_link *page_point = pt_point->top;
				for (UInt i4 = 0; i4 < pt_point->used; i4++, page_point = page_point->next) {
					UShort index = page_point->index;
					PAGE_link *page_l = new PAGE_link;
					memset(page_l, 0, sizeof(PAGE_link));
					if (!pt->pt) {
						pt->pt = (PAGE**)malloc(pt_point->size * 8);
						memset(pt->pt, 0, pt_point->size * 8);
					}
					pt->pt[index] = pt_point->pt[index];//copy
					(pt->pt[index])->used_point += 1;
					{
						PAGE_link *orignal = (pt)->top;
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
	ULong max = (address + length - 1)&(~0xfff);
	address &= (~0xfff);
#ifdef OPSTR
	int freecount = 0;
#endif
	while (address <= max) {
		PDPT **pdpt = (*CR3)->pt + (address >> 39 & 0x1ff);
		if (!*pdpt) {
			return address;
		}
		PDT **pdt = (*pdpt)->pt + (address >> 30 & 0x1ff);
		if (!*pdt) {
			return address;
		}
		PT **pt = (*pdt)->pt + (address >> 21 & 0x1ff);
		if (!*pt) {
			return address;
		}
		UShort PT_ind = (address >> 12 & 0x1ff);
		PAGE **page = (*pt)->pt + PT_ind;
		if (*page) {
			PAGE_link *page_l = (*pt)->top;
			for (UInt i = 0; i < (*pt)->used; i++, page_l = page_l->next) {
				if ((page_l) && (page_l->index == PT_ind)) {
					{
						PAGE_link *p = (page_l)->prev;
						PAGE_link *n = (page_l)->next;
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
			delete *pdpt;
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

inline PAGE* MEM::getMemPage(Addr64 address) {
	
	return GETPAGE(address);
	
}

inline void MEM::CheckSelf(PAGE *&P, Addr64 address)
{
	if (user != P->user) {//WNC
		if (P->user == -1ull) {
			vassert(P->unit == NULL);
			P->unit = new Register<0x1000>(m_ctx, need_record);
			P->user = user;
			mem_change_map[ALIGN((Addr64)address, 0x1000)] = P->unit;
			return;
		}
		Addr64 e_address = address;
		PT *pt = GETPT(e_address);
		auto ptindex = (e_address >> 12 & 0x1ff);
		PAGE **page = pt->pt + ptindex;
		PAGE_link *pl = pt->top;
		*page = new PAGE;
		(*page)->unit = new Register<0x1000>(*(P->unit), m_ctx, need_record);

		--P->used_point;//线程锁
		P = (*page);
		P->user = user;
		P->used_point = 1;
		mem_change_map[ALIGN((Addr64)address, 0x1000)] = (*page)->unit;
	}
}


inline Vns linearGet(PAGE *P, UInt offset, UInt length) {

	if (length >= 8) {
		return P->unit->Iex_Get(offset, Ity_I64);
	}
	else if (length >= 4) {
		return P->unit->Iex_Get(offset, Ity_I32);
	}
	else if (length >= 2) {
		return P->unit->Iex_Get(offset, Ity_I16);
	}
	else {
		return P->unit->Iex_Get(offset, Ity_I8);
	}
}


template<memTAG T>
inline void linearPut(PAGE *P, UInt offset, UInt length, Vns &data) {
	UInt plength = length;
	while (plength != 0) {
		if (plength >= 8) {
			P->unit->Ist_Put<T>(offset , data.Split(8, length - plength));
			plength -= 8;
			offset += 8;
		}
		else if (plength >= 4) {
			P->unit->Ist_Put<T>(offset , data.Split(4, length - plength));
			plength -= 4;
			offset += 4;
		}
		else if (plength >= 2) {
			P->unit->Ist_Put<T>(offset , data.Split(2, length - plength));
			plength -= 2;
			offset += 2;
		}
		else {
			P->unit->Ist_Put<T>(offset , data.Split(1, length - plength));
			plength -= 1;
			offset += 1;
		}
	}
}
	

// ty  IRType || n_bits
template<IRType ty>
inline Vns MEM::Iex_Load(Addr64 address)
{
	PAGE *P = getMemPage(address);
	UShort offset = (UShort)address & 0xfff;
	UShort size;
	if (user == P->user) {//WNC
		switch (ty) {
		case 8:
		case Ity_I8:														 
			return P->unit->Iex_Get<Ity_I8  >(offset);
		case 16:
		case Ity_I16: {
			if (offset >= 0xfff) { 
				size = 2; goto linear_err1; 
			};
			return P->unit->Iex_Get<Ity_I16 >(offset);
		}
		case 32:
		case Ity_F32:
		case Ity_I32: {
			if (offset >= 0xffd) {
				size = 4; 
				goto linear_err1; 
			};
			return P->unit->Iex_Get<Ity_I32>(offset); 
		}
		case 64:
		case Ity_F64:
		case Ity_I64: {
			if (offset >= 0xff9) { 
				size = 8; goto linear_err1; 
			};
			return P->unit->Iex_Get<Ity_I64>(offset);
		}
		case 128:
		case Ity_I128:
		case Ity_V128: {
			if (offset >= 0xff1) { 
				size = 16; 
				goto linear_err1; 
			}; 
			return P->unit->Iex_Get<Ity_V128>(offset);
		}
		case 256:
		case Ity_V256: {
			if (offset >= 0xfe1) { 
				size = 32; 
				goto linear_err1; 
			};
			return P->unit->Iex_Get<Ity_V256>(offset);
		}
		default:vpanic("2333333");
		}
	linear_err1:
		{
			PAGE *nP = getMemPage((Addr64)address + 0x1000);

			UInt plength = 0x1000 - offset;
			UInt pIndex = plength;
			UInt npLength = size - plength;
			UInt npIndex = npLength;

			Vns result = linearGet(P, offset, pIndex);
			pIndex -= (result.bitn >> 3);
			while (pIndex != 0) {
				Vns g = linearGet(P, 0x1000 - pIndex, pIndex);
				pIndex -= (g.bitn >> 3);
				result = g.Concat(result);
			}
			if (nP->user == user) {
				while (npIndex != 0) {
					Vns g = linearGet(P, npLength - npIndex, npIndex);
					npIndex -= (g.bitn >> 3);
					result = g.Concat(result);
				}
			}
			else {
				while (npIndex != 0) {
					Vns g = linearGet(P, npLength - npIndex, npIndex).translate(m_ctx);
					npIndex -= (g.bitn >> 3);
					result = g.Concat(result);
				}
			}
			return result;
		}
	}
	else {
		switch (ty) {
		case Ity_I8:														return P->unit->Iex_Get<Ity_I8 >(offset, m_ctx);
		case Ity_I16: if (offset >= 0xfff) { size = 2; goto linear_err2; }; return P->unit->Iex_Get<Ity_I16>(offset, m_ctx);
		case Ity_F32:
		case Ity_I32: if (offset >= 0xffd) { size = 4; goto linear_err2; }; return P->unit->Iex_Get<Ity_I32>(offset, m_ctx);;
		case Ity_F64:
		case Ity_I64: if (offset >= 0xff9) { size = 8; goto linear_err2; }; return P->unit->Iex_Get<Ity_I64>(offset, m_ctx);;
		case Ity_I128:
		case Ity_V128:if (offset >= 0xff1) { size = 16; goto linear_err2; }; return P->unit->Iex_Get<Ity_V128>(offset, m_ctx);;
		case Ity_V256:if (offset >= 0xfe1) { size = 32; goto linear_err2; }; return P->unit->Iex_Get<Ity_V256>(offset, m_ctx);;
		default:vpanic("2333333");
		}

	linear_err2:
		{
			PAGE *nP = getMemPage((Addr64)address + 0x1000);

			UInt plength = 0x1000 - offset;
			UInt pIndex = plength;
			UInt npLength = size - plength;
			UInt npIndex = npLength;

			Vns result = linearGet(P, offset, pIndex).translate(m_ctx);
			pIndex -= (result.bitn >> 3);
			while (pIndex != 0) {
				Vns g = linearGet(P, 0x1000 - pIndex, pIndex).translate(m_ctx);
				pIndex -= (g.bitn >> 3);
				result = g.Concat(result);
			}
			if (nP->user == user) {
				while (npIndex != 0) {
					Vns g = linearGet(P, npLength - npIndex, npIndex);
					npIndex -= (g.bitn >> 3);
					result = g.Concat(result);
				}
			}
			else {
				while (npIndex != 0) {
					Vns g = linearGet(P, npLength - npIndex, npIndex).translate(m_ctx);
					npIndex -= (g.bitn >> 3);
					result = g.Concat(result);
				}
			}
			return result;
		}
	}
}




inline Vns MEM::Iex_Load(Addr64 address, IRType ty)
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

template<IRType ty>
inline Vns MEM::Iex_Load(Z3_ast address) {
	std::vector<Z3_ast> saddrs;
	eval_all(saddrs, *m_solv, address);
	Z3_ast ast_address = address;

	auto it = saddrs.begin();
	auto end = saddrs.end();
	uint64_t Z3_RE;
	if (!Z3_get_numeral_uint64(m_ctx, *it, &Z3_RE)) vassert(0);
	Vns data = Iex_Load<ty>(Z3_RE);
	Z3_ast reast = data;
	Z3_inc_ref(m_ctx, reast);
	it++;
	while (it != end) {
		auto addr = *it;
		if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
		data = Iex_Load<ty>(Z3_RE);
		auto eq = Z3_mk_eq(m_ctx, address, addr);
		Z3_inc_ref(m_ctx, eq);
		auto ift = Z3_mk_ite(m_ctx, eq, data, reast);
		Z3_inc_ref(m_ctx, ift);
		Z3_dec_ref(m_ctx, reast);
		Z3_dec_ref(m_ctx, eq);
		Z3_dec_ref(m_ctx, addr);
		reast = ift;
		it++;
	}
	Z3_dec_ref(m_ctx, reast);
	return Vns(m_ctx, reast);
}

template<IRType ty>
inline Vns MEM::Iex_Load(Vns const &address) {
	if (address.real()) {
		return Iex_Load<ty>((Addr64)address);
	}
	else {
		return Iex_Load<ty>((Z3_ast)address);
	}
}

inline Vns MEM::Iex_Load(Z3_ast address, IRType ty) {
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
	default:vpanic("2333333");
	}
}
inline Vns MEM::Iex_Load(Vns const &address, IRType ty)
{
	if (address.real()) {
		return Iex_Load((Addr64)address, ty);
	}
	else {
		return Iex_Load((Z3_ast)address, ty);
	}
}


template<typename DataTy>
inline void MEM::Ist_Store(Addr64 address, DataTy data) {
	PAGE *P = getMemPage(address);
	CheckSelf(P, address);
	UShort offset = address & 0xfff;
	if (fastalignD1[sizeof(data)<<3] > 0xFFF - offset) {
		PAGE *nP = getMemPage((ULong)address + 0x1000);
		UInt plength = 0x1000 - offset;
		UInt npLength = sizeof(data) - plength;
		/*linearPut<numreal>(P, offset, plength, data);
		linearPut<numreal>(nP, 0, npLength, data.Split(npLength, plength));*/
	}
	else {
		P->unit->Ist_Put(offset, data);
	}
}

template<unsigned int bitn>
inline void MEM::Ist_Store(Addr64 address, Z3_ast data) {
	PAGE *P = getMemPage(address);
	CheckSelf(P, address);
	UShort offset = address & 0xfff;
	if (fastalignD1[bitn] > 0xFFF - offset) {
		PAGE *nP = getMemPage((ULong)address + 0x1000);
		UInt plength = 0x1000 - offset;
		UInt npLength = (bitn >> 3) - plength;
		//linearPut<symbolic>(P, offset, plength, data);
		//linearPut<symbolic>(nP, 0, npLength, data.Split(npLength, plength));
	}
	else {
		P->unit->Ist_Put<bitn>(offset, data);
	}
}

template<typename DataTy>
inline void MEM::Ist_Store(Z3_ast address, DataTy data) {
	std::vector<Z3_ast> saddrs;
	if (eval_all(saddrs, *m_solv, address) > 1) {
		for (auto addr : saddrs) {
			uint64_t Z3_RE;
			if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
			auto oData = Iex_Load<(IRType)(sizeof(DataTy) << 3)>(Z3_RE);
			auto eq = Z3_mk_eq(m_ctx, address, addr);
			Z3_inc_ref(m_ctx, eq);
			auto n_Data = Z3_mk_ite(m_ctx, eq, Vns(m_ctx, data), oData);
			Z3_inc_ref(m_ctx, n_Data);
			Ist_Store<(IRType)(sizeof(DataTy) << 3)>(Z3_RE, n_Data);
			Z3_dec_ref(m_ctx, n_Data);
			Z3_dec_ref(m_ctx, eq);
			Z3_dec_ref(m_ctx, addr);
		}
	}
	else {
		uint64_t Z3_RE;
		if (!Z3_get_numeral_uint64(m_ctx, saddrs[0], &Z3_RE)) vassert(0);
		Ist_Store(Z3_RE, data);
	}
}
//n_bit
template<unsigned int bitn>
inline void MEM::Ist_Store(Z3_ast address, Z3_ast data) {
	std::vector<Z3_ast> saddrs;
	if (eval_all(saddrs, *m_solv, address) > 1) {
		for (auto addr : saddrs) {
			uint64_t Z3_RE;
			if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
			auto oData = Iex_Load<(IRType)bitn>(Z3_RE);
			auto eq = Z3_mk_eq(m_ctx, address, addr);
			Z3_inc_ref(m_ctx, eq);
			auto ndata = Z3_mk_ite(m_ctx, eq, data, oData);
			Z3_inc_ref(m_ctx, ndata);
			Ist_Store<bitn>(Z3_RE, ndata);
			Z3_dec_ref(m_ctx, ndata);
			Z3_dec_ref(m_ctx, eq);
			Z3_dec_ref(m_ctx, addr);
		}
	}
	else {
		uint64_t Z3_RE;
		if (!Z3_get_numeral_uint64(m_ctx, saddrs[0], &Z3_RE)) vassert(0);
		Ist_Store<bitn>(Z3_RE, data);
	}
}


inline void MEM::Ist_Store(Addr64 address, Vns const &data) {
	if (data.real()) {
		switch (data.bitn) {
		case 8:  Ist_Store(address, (UChar)data); break;
		case 16: Ist_Store(address, (UShort)data); break;
		case 32: Ist_Store(address, (UInt)data); break;
		case 64: Ist_Store(address, (ULong)data); break;
		case 128: Ist_Store(address, (__m128i)data); break;
		case 256: Ist_Store(address, (__m256i)data); break;
		default:vpanic("2333333");
		}
	}
	else {
		switch (data.bitn) {
		case 8:  Ist_Store<8>(address, (Z3_ast)data); break;
		case 16: Ist_Store<16>(address, (Z3_ast)data); break;
		case 32: Ist_Store<32>(address, (Z3_ast)data); break;
		case 64: Ist_Store<64>(address, (Z3_ast)data); break;
		case 128: Ist_Store<128>(address, (Z3_ast)data); break;
		case 256: Ist_Store<256>(address, (Z3_ast)data); break;
		default:vpanic("2333333");
		}
	}
}


template<typename DataTy>
inline void MEM::Ist_Store(Vns const &address, DataTy data) {
	if (address.real()) {
		Ist_Store((Addr64)address, data);
	}
	else {
		Ist_Store((Z3_ast)address, data);
	}
}



inline void MEM::Ist_Store(Z3_ast address, Vns const &data) {
	if (data.real()) {
		switch (data.bitn) {
		case 8: return Ist_Store(address, (UChar)data);
		case 16:return Ist_Store(address, (UShort)data);
		case 32:return Ist_Store(address, (UInt)data);
		case 64:return Ist_Store(address, (ULong)data);
		case 128:return Ist_Store(address, (__m128i)data);
		case 256:return Ist_Store(address, (__m256i)data);
		default:vpanic("2333333");
		}
	}
	else {
		switch (data.bitn) {
		case 8: return Ist_Store<8>(address, (Z3_ast)data);
		case 16:return Ist_Store<16>(address, (Z3_ast)data);
		case 32:return Ist_Store<32>(address, (Z3_ast)data);
		case 64:return Ist_Store<64>(address, (Z3_ast)data);
		case 128:return Ist_Store<128>(address, (Z3_ast)data);
		case 256:return Ist_Store<256>(address, (Z3_ast)data);
		default:vpanic("2333333");
		}
	}
}

inline void MEM::Ist_Store(Vns const &address, Vns const &data) {
	if (address.real()) {
		Ist_Store((Addr64)address, data);
	}
	else {
		Ist_Store((Z3_ast)address, data);
	}
}

inline void MEM::write_bytes(ULong address, ULong length, unsigned char *data) {
	ULong max = address + length;
	PAGE *p_page = GETPAGE(address);
	if (!p_page->unit) {
		p_page->unit = new Register<0x1000>(m_ctx,need_record);
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
}
inline void MEM::set_double_page(Addr64 address, Pap &addrlst) {
	addrlst.Surplus = 0x1000 - (address & 0xfff);
	addrlst.t_page_addr = (UChar*)GETPAGE((ULong)address)->unit->m_bytes + (address & 0xfff);
	addrlst.n_page_mem = (UChar*)GETPAGE((ULong)(address + 0x1000))->unit->m_bytes;
}




#undef GETPT
#undef GETPAGE
#undef COPY_SYM
#undef LCODEDEF1
#undef LCODEDEF2
#undef LCODEDEF3
#undef LCODEDEF4
#undef LCODEDEF5
#undef LMAX1
#undef LMAX2
#undef LMAX3
#undef LMAX4
#undef LMAX5
#undef LIND1
#undef LIND2
#undef LIND3
#undef LIND4
#undef LTAB1
#undef LTAB2
#undef LTAB3
#undef LTAB4
#undef LTAB5
#undef LSTRUCT1
#undef LSTRUCT2
#undef LSTRUCT3
#undef LSTRUCT4
#undef LSTRUCT5

#endif // !MEM_H