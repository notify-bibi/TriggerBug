#ifndef MEM_H
#define MEM_H

using namespace z3;
#include "memory_CD.hpp"

static UInt newDifUser()
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

inline Variable linearGet(PAGE *P, UInt offset, UInt length) {

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
inline Variable linearGetTranslate(PAGE *P, UInt offset, UInt length, Z3_context m_ctx) {
	if (length >= 8) {
		return P->unit->Iex_Get_Translate(offset, Ity_I64, m_ctx);
	}
	else if (length >= 4) {
		return P->unit->Iex_Get_Translate(offset, Ity_I32, m_ctx);
	}
	else if (length >= 2) {
		return P->unit->Iex_Get_Translate(offset, Ity_I16, m_ctx);
	}
	else {
		return P->unit->Iex_Get_Translate(offset, Ity_I8, m_ctx);
	}
}

template<memTAG T>
inline void linearPut(PAGE *P, UInt offset, UInt length, Variable &data) {
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
	



inline Variable MEM::Iex_Load(Variable &address, IRType ty)
{
	if (address.real()) {
		PAGE *P = getMemPage(address);
		UShort offset = (UShort)address & 0xfff;
		UShort size;
		if (user == P->user) {//WNC
			switch (ty) {
			case Ity_I8:return P->unit->Iex_Get(offset, Ity_I8);;
			case Ity_I16: if (offset >= 0xfff) { size = 2 ; goto linear_err1; }; return P->unit->Iex_Get(offset, Ity_I16);;
			case Ity_F32:
			case Ity_I32: if (offset >= 0xffd) { size = 4 ; goto linear_err1; }; return P->unit->Iex_Get(offset, Ity_I32);;
			case Ity_F64:
			case Ity_I64: if (offset >= 0xff9) { size = 8 ; goto linear_err1; }; return P->unit->Iex_Get(offset, Ity_I64);;
			case Ity_I128:
			case Ity_V128:if (offset >= 0xff1) { size = 16; goto linear_err1; }; return P->unit->Iex_Get(offset, Ity_V128);;
			case Ity_V256:if (offset >= 0xfe1) { size = 32; goto linear_err1; }; return P->unit->Iex_Get(offset, Ity_V256);;
			default:vpanic("2333333");
			}
		linear_err1:
			{
				PAGE *nP = getMemPage((Addr64)address + 0x1000);

				UInt plength = 0x1000 - offset;
				UInt pIndex = plength;
				UInt npLength = size - plength;
				UInt npIndex = npLength;

				Variable result = linearGet(P, offset, pIndex);
				pIndex -= (result.bitn >> 3);
				while (pIndex != 0) {
					Variable g = linearGet(P, 0x1000 - pIndex, pIndex);
					pIndex -= (g.bitn >> 3);
					result = g.Concat(result);
				}
				if (nP->user == user) {
					while (npIndex != 0) {
						Variable g = linearGet(P, npLength - npIndex, npIndex);
						npIndex -= (g.bitn >> 3);
						result = g.Concat(result);
					}
				}
				else {
					while (npIndex != 0) {
						Variable g = linearGetTranslate(P, npLength - npIndex, npIndex, m_ctx);
						npIndex -= (g.bitn >> 3);
						result = g.Concat(result);
					}
				}
				return result;
			}
		}
		else {
			switch (ty) {
			case Ity_I8:return P->unit->Iex_Get_Translate(offset, Ity_I8, m_ctx);
			case Ity_I16: if (offset >= 0xfff) { size = 2 ; goto linear_err2; }; return P->unit->Iex_Get_Translate(offset, Ity_I16, m_ctx);
			case Ity_F32:
			case Ity_I32: if (offset >= 0xffd) { size = 4 ; goto linear_err2; }; return P->unit->Iex_Get_Translate(offset, Ity_I32, m_ctx);;
			case Ity_F64:
			case Ity_I64: if (offset >= 0xff9) { size = 8 ; goto linear_err2; }; return P->unit->Iex_Get_Translate(offset, Ity_I64, m_ctx);;
			case Ity_I128:
			case Ity_V128:if (offset >= 0xff1) { size = 16; goto linear_err2; }; return P->unit->Iex_Get_Translate(offset, Ity_V128, m_ctx);;
			case Ity_V256:if (offset >= 0xfe1) { size = 32; goto linear_err2; }; return P->unit->Iex_Get_Translate(offset, Ity_V256, m_ctx);;
			default:vpanic("2333333");
			}

		linear_err2:
			{
				PAGE *nP = getMemPage((Addr64)address + 0x1000);

				UInt plength = 0x1000 - offset;
				UInt pIndex = plength;
				UInt npLength = size - plength;
				UInt npIndex = npLength;

				Variable result = linearGetTranslate(P, offset, pIndex, m_ctx);
				pIndex -= (result.bitn >> 3);
				while (pIndex != 0) {
					Variable g = linearGetTranslate(P, 0x1000 - pIndex, pIndex, m_ctx);
					pIndex -= (g.bitn >> 3);
					result = g.Concat(result);
				}
				if (nP->user == user) {
					while (npIndex != 0) {
						Variable g = linearGet(P, npLength - npIndex, npIndex);
						npIndex -= (g.bitn >> 3);
						result = g.Concat(result);
					}
				}
				else {
					while (npIndex != 0) {
						Variable g = linearGetTranslate(P, npLength - npIndex, npIndex, m_ctx);
						npIndex -= (g.bitn >> 3);
						result = g.Concat(result);
					}
				}
				return result;
			}
		}
		
	}
	else {
		std::vector<Z3_ast> saddrs;
		eval_all(saddrs, *m_solv, address );
		Z3_ast ast_address = address;
		
		auto it = saddrs.begin();
		auto end = saddrs.end();
		uint64_t Z3_RE;
		if (!Z3_get_numeral_uint64(m_ctx, *it, &Z3_RE)) vassert(0);
		Variable data = Iex_Load(Variable(Z3_RE, m_ctx, 64), ty);
		Z3_ast reast = data;
		Z3_inc_ref(m_ctx, reast);
		it++;
		while (it != end) {
			auto addr = *it;
			if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
			data = Iex_Load(Variable(Z3_RE, m_ctx, 64), ty);
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
		return Variable(address, False, reast);
	}
}



template<>
inline void MEM::Ist_Store<e_real, e_real>(Variable &address, Variable &data) {
#ifdef debug
	address.tostr();
#endif
#ifdef _DEBUG
	vassert(address.real() && data.real());
#endif
	PAGE *P = getMemPage(address);
	CheckSelf(P, address);
	UShort offset = (UShort)address & 0xfff;
	
	if (fastalignD1[data.bitn] > 0xFFF - offset) {
		PAGE *nP = getMemPage((ULong)address + 0x1000);
		
		UInt plength = 0x1000 - offset;
		UInt npLength = (data.bitn>>3) - plength;
		linearPut<e_real>(P, offset, plength, data);
		linearPut<e_real>(nP, 0, npLength, data.Split(npLength, plength));
	}
	else {
		P->unit->Ist_Put<e_real>(offset, data);
	}
	
}
template<>
inline void MEM::Ist_Store<e_real, e_symbolic>(Variable &address, Variable &data) {
#ifdef Debug
	address.tostr();
#endif
#ifdef _DEBUG
	vassert(address.real() && data.symbolic());
#endif
	PAGE *P = getMemPage(address);
	CheckSelf(P, address);
	UShort offset = (UShort)address & 0xfff;
	if (fastalignD1[data.bitn] > 0xFFF - offset) {
		PAGE *nP = getMemPage((ULong)address + 0x1000);
		UInt plength = 0x1000 - offset;
		UInt npLength = (data.bitn >> 3) - plength;
		linearPut<e_symbolic>(P, offset, plength, data);
		linearPut<e_symbolic>(nP, 0, npLength, data.Split(npLength, plength));
	}
	else {
		P->unit->Ist_Put<e_symbolic>(offset, data);
	}
	

}
template<>
inline void MEM::Ist_Store<e_symbolic, e_real>(Variable &address, Variable &data) {\

#ifdef _DEBUG
vassert(address.symbolic() && data.real());
#endif
	std::vector<Z3_ast> saddrs;
	if (eval_all(saddrs, *m_solv, address) > 1) {
		auto ty = length2ty(data.bitn);
		for (auto addr : saddrs) {
			uint64_t Z3_RE;
			if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
			auto Vaddr = Variable(Z3_RE, m_ctx, 64);
			auto oData = Iex_Load(Vaddr, ty);
			auto eq = Z3_mk_eq(m_ctx, address, addr);
			Z3_inc_ref(m_ctx, eq);
			Ist_Store<e_real, e_symbolic>(Vaddr, Variable(m_ctx, Z3_mk_ite(m_ctx, eq, data, oData), data.bitn));
			Z3_dec_ref(m_ctx, eq);
			Z3_dec_ref(m_ctx, addr);
		}
	}
	else {
		uint64_t Z3_RE;
		if (!Z3_get_numeral_uint64(m_ctx, saddrs[0], &Z3_RE)) vassert(0);
		Ist_Store<e_real, e_real>(Variable(Z3_RE, m_ctx, 64), data);
	}
	
}
template<>
inline void MEM::Ist_Store<e_symbolic, e_symbolic>(Variable &address, Variable &data) {

#ifdef _DEBUG
	vassert(address.symbolic() && data.symbolic());
#endif
	std::vector<Z3_ast> saddrs;
	if (eval_all(saddrs, *m_solv, address) > 1) {
		auto ty = length2ty(data.bitn);
		for (auto addr : saddrs) {
			uint64_t Z3_RE;
			if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
			auto Vaddr = Variable(Z3_RE, m_ctx, 64);
			auto oData = Iex_Load(Vaddr, ty);
			auto eq = Z3_mk_eq(m_ctx, address, addr);
			Z3_inc_ref(m_ctx, eq);
			Ist_Store<e_real, e_symbolic>(Vaddr, Variable(m_ctx, Z3_mk_ite(m_ctx, eq, data, oData), data.bitn));
			Z3_dec_ref(m_ctx, eq);
			Z3_dec_ref(m_ctx, addr);
		}
	}
	else {
		uint64_t Z3_RE;
		if (!Z3_get_numeral_uint64(m_ctx, saddrs[0], &Z3_RE)) vassert(0);
		Ist_Store<e_real, e_symbolic>(Variable(Z3_RE, m_ctx, 64), data);
	}
}


inline void MEM::Ist_Store(Variable &address, Variable &data) {
	if (data.real()) {
		address.real() ?
			data.real() ? Ist_Store<e_real, e_real>(address, data) : Ist_Store<e_real, e_symbolic>(address, data)
			:
			data.real() ? Ist_Store<e_symbolic, e_real>(address, data) : Ist_Store<e_symbolic, e_symbolic>(address, data);
	}
	else {
		auto sdata = data.simplify();
		address.real() ?
			sdata.real() ? Ist_Store<e_real, e_real>(address, sdata) : Ist_Store<e_real, e_symbolic>(address, sdata)
			:
			sdata.real() ? Ist_Store<e_symbolic, e_real>(address, sdata) : Ist_Store<e_symbolic, e_symbolic>(address, sdata);
	}
}

inline void MEM::Ist_Store_R(Addr64 address, Variable &data) {
	if (data.real()) {
		Ist_Store<e_real, e_real>(Variable(address, data), data);
	}
	else {
		Ist_Store<e_real, e_symbolic>(Variable(address, data), data);
	}
}

inline void MEM::CheckSelf(PAGE *&P, Variable &address)
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
		mem_change_map[ALIGN((Addr64)address, 0x1000)]= (*page)->unit;
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