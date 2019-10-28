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
    WXC 2019-10-28
Revision History:
--*/
#ifndef MEMORY_DEFS_H
#define MEMORY_DEFS_H

#include "../engine.hpp"
#include "Variable.hpp"
#include "Register.hpp"

using namespace z3;
extern UInt global_user;
extern std::mutex global_user_mutex;

#ifdef _DEBUG
#define NEED_VERIFY 
#endif
#define TRACE_AM

#define BIT_BLAST_MAX_BIT 14


class addressingMode
{
public:
    enum addressingModeKind {
        cant_analysis = 0,
        found_base_and_offset,
        support_bit_blast
    };

private:
    struct sbit_struct {
        Z3_ast sym_ast;
        bool rbit;
        UInt idx;
    };

    struct sbit_struct_r {
        sbit_struct sbit;
        ADDR sign_mask;
        UInt nbit;
    };

    class iterator
    {
        struct shift_mask {
            UChar shift;
            ADDR mask;
        };

    private:
        ADDR m_sym_mask;
        ADDR m_or_mask;
        ADDR tmp_bit_blast;
        ADDR tmp_target_bit_blast;
        struct shift_mask m_sym_ml[BIT_BLAST_MAX_BIT];
        UInt m_sym_ml_n;


        struct shift_mask m_sign_ml[32];
        UInt m_sign_ml_n;

    public:
        inline iterator() {};

        inline iterator(addressingMode &am) :
            m_sym_mask(am.m_sym_mask),
            m_or_mask(am.m_or_mask),
            tmp_bit_blast((ADDR)0),
            tmp_target_bit_blast((ADDR)0),
            m_sym_ml_n(0),
            m_sign_ml_n(0)
        {
            DWORD N;
            UInt _pcur;
            UInt nb = 0;
            if (_BitScanForward64(&N, m_sym_mask)) {
                m_sym_ml[0] = shift_mask{ N,((ADDR)1) << N };
                m_sym_ml_n = 1;
                _pcur = N;
                tmp_target_bit_blast = ((ADDR)1);
                nb = 1;

                for (; ; ) {
                    if (_BitScanForward64(&N, m_sym_mask & fastMaskReverseI1[_pcur])) {
                        if (N = _pcur + 1) {
                            m_sym_ml[m_sym_ml_n - 1].mask |= ((ADDR)1) << N;
                        }
                        else {
                            m_sym_ml[m_sym_ml_n - 1] = shift_mask{ N,((ADDR)1) << N };
                            m_sym_ml_n++;
                        }
                        tmp_target_bit_blast |= ((ADDR)1) << (nb++);
                        _pcur = N;
                    }
                    else {
                        break;
                    }
                }
            }

        parse_sign:
            for (auto s : am.m_sign_mask) {
                m_sign_ml[m_sign_ml_n++] = shift_mask{ nb, s };
                tmp_target_bit_blast |= ((ADDR)1) << (nb++);
            }
            tmp_target_bit_blast += 1;
        }


        inline bool operator!=(const iterator& src)
        {
            return tmp_bit_blast != tmp_target_bit_blast;
        }

        inline void operator++()
        {
            tmp_bit_blast++;
        }

        inline ADDR operator*()
        {
            ADDR re = 0;
            for (UInt sign_ml_n = 0; sign_ml_n < m_sign_ml_n; sign_ml_n++) {
                if (tmp_bit_blast >> m_sign_ml[sign_ml_n].shift) {
                    re |= m_sign_ml[sign_ml_n].mask;
                }
            }
            for (UInt sym_ml_n = 0; sym_ml_n < m_sym_ml_n; sym_ml_n++) {
                re |= (tmp_bit_blast << m_sym_ml[sym_ml_n].shift) & m_sym_ml[sym_ml_n].mask;
            }
            return re | m_or_mask;
        }
    };



private:
    context& m_ctx;
    expr m_symbolic;
    ADDR m_base;
    expr m_offset;

    std::vector<ADDR> m_sign_mask;
    ADDR m_sym_mask;
    UInt m_sym_mask_n;
    ADDR m_or_mask;

    addressingModeKind m_analysis_kind;
public:
    addressingMode(const expr& e) :
        m_ctx(e.ctx()),
        m_symbolic(e),
        m_sym_mask(0ull),
        m_or_mask(0ull),
        m_sym_mask_n(0),
        m_offset(m_ctx)
    {
        if (ast2baseAoffset()) {
            if (offset_bit_blast()) {
                m_analysis_kind = support_bit_blast;
            }
            else {
                m_analysis_kind = found_base_and_offset;
            }
        }
        else {
            m_analysis_kind = cant_analysis;
        }
    }
private:
    bool ast2baseAoffset() {
        //std::cout << saddr.simplify() << std::endl << std::endl;
        expr base = expr(m_ctx);
        m_offset = _ast2base(base, m_symbolic, 0, 6);
        //std::cout << idx << std::endl;
        if (base.simplify().is_numeral_u64(m_base)) {
#if defined(NEED_VERIFY)
            if (m_base > 100) {
                Int is_right;
                expr eval = base + m_offset == m_symbolic;
                if (ite(eval, m_ctx.bv_val(1, 8), m_ctx.bv_val(0, 8)).simplify().is_numeral_i(is_right)) {
                    if (is_right) {
                        return true;
                    }
                    else {
                        goto faild;
                    }
                }
                else {
                    vex_printf("cant determine base %p try solver:\n", m_base);
                }
                solver s(m_ctx);
                s.add(!eval);
                if (s.check() == unsat) {
                    return true;
                }
                std::cout << "unsat model:\n" << s.get_model() << std::endl;
                goto faild;
            }
#else
                return true;
#endif
        }
        return false;
faild:
        std::cout << "symbolic:\n" << m_symbolic << std::endl << std::endl;
        std::cout << "symbolic.simplify:\n" << m_symbolic.simplify() << std::endl << std::endl;

        std::cout << "base:\n" << m_base << std::endl << std::endl;
        std::cout << "Index:\n" << m_offset << std::endl << std::endl;

        vex_printf("is False  %p\n", m_base);
        vpanic("sorry .engine error.  report me and i will fix it\n");
    }


    bool offset_bit_blast() {
        z3::sort so = m_offset.get_sort();
        UInt size = so.bv_size();

        std::vector<sbit_struct_r> vec;
        for (UInt idx = 0; idx < size; idx++) {
            sbit_struct s = check_is_extract(m_offset, idx);
            if (s.sym_ast) {
                auto end = vec.end();
                auto m = vec.begin();
                bool exist = false;
                while (m != end) {
                    if (s.sym_ast == m->sbit.sym_ast && s.idx == m->sbit.idx) {
                        m->sign_mask |= ((ADDR)1) << idx;
                        m->nbit++;
                        exist = true;
                        break;
                    }
                    m++;
                };
                if (!exist) {
                    vec.emplace_back(sbit_struct_r{ s  , ((ADDR)1) << idx, 1 });
                };
            }
            else {
                m_or_mask = m_or_mask | ((ADDR)s.rbit << idx);
            }
        }

        
        auto end = vec.end();
        auto m = vec.begin();
        while (m != end) {
            if (m->nbit == 1) {
                m_sym_mask |= m->sign_mask;
                m_sym_mask_n++;
            }
            else {
                m_sign_mask.emplace_back(m->sign_mask);
            }
            m++;
        }
        return ((m_sym_mask_n + m_sign_mask.size()) >= BIT_BLAST_MAX_BIT) ? false : true;
    }

public:
    addressingModeKind analysis_kind() {
        return m_analysis_kind;
    }


    inline ADDR getBase() {
        assert(m_analysis_kind != cant_analysis);
        return m_base;
    }

    inline expr getoffset() {
        assert(m_analysis_kind != cant_analysis);
        return m_offset;
    }

    inline addressingMode(const addressingMode& a) :
        m_ctx(a.m_ctx),
        m_offset(a.m_offset),
        m_base(a.m_base),
        m_symbolic(a.m_symbolic)
    {

    }

    inline void operator=(const addressingMode& a)
    {
        this->~addressingMode();
        m_offset = a.m_offset;
        m_base = a.m_base;
        m_symbolic = a.m_symbolic;
    }

    inline ~addressingMode() {
    }


    inline iterator begin() {
        assert(m_analysis_kind == support_bit_blast);
        return iterator(*this);
    }

    inline iterator end() {
        return iterator();
    }

    void print() {
        printf("\tor_mask: %016x\t\t", m_or_mask);
        printf("sym_mask: n:%d %016x\n", m_sym_mask_n, m_sym_mask);
        if (!m_sign_mask.empty()) {
            printf("sign_mask: \n\t{\n", m_or_mask);
            for (auto sm : m_sign_mask) {
                printf("\t\t %016x\n", sm);
            }
            printf("\n\t}\n", m_or_mask);
        }
    }
private:
    static expr _ast2base(expr& base,
        expr const& e,
        UInt deep, UInt max_deep
    );

    static sbit_struct check_is_extract(expr const& e, UInt idx);
};


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



typedef struct PAGE {
    ULong user;
    UInt used_point;
    bool unit_mutex;
    Register<0x1000> *unit;
}PAGE;

typedef struct PAGE_link {
    UShort index;
    PAGE_link *prev;
    PAGE_link *next;
}PAGE_link;

typedef struct PT {
    UShort used;
    UShort index;
    PAGE_link *top;
    PT *prev;
    PT *next;
    UInt size;
    PAGE **pt;
}PT;

typedef struct PDT {
    UShort used;
    UShort index;
    PT *top;
    PDT *prev;
    PDT *next;
    UInt size;
    PT **pt;
}PDT;

typedef struct PDPT {
    UShort used;
    UShort index;
    PDT *top;
    PDPT *prev;
    PDPT *next;
    UInt size;
    PDT **pt;
}PDPT;

typedef struct PML4T {
    UShort used;
    PDPT *top;
    UInt size;
    PDPT **pt;
}PML4T;

class MEM {
    friend class State;
public:
    class Itaddress {
    private:
        solver& m_solver;
        context& m_ctx;
        Z3_ast m_addr;
        Z3_ast last_avoid_addr;
        UShort m_nbit;
        std::vector<Z3_model> v_model;
    public:
        Z3_lbool m_lbool;
        inline Itaddress(solver& s, Z3_ast addr) :m_ctx(m_solver.ctx()), m_solver(s), m_addr(addr), m_nbit(Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_addr))) {
            m_addr = Z3_simplify(s.ctx(), m_addr);
            Z3_inc_ref(m_ctx, m_addr);
            m_solver.push();
            Z3_ast so = Z3_mk_bvugt(m_ctx, m_addr, m_ctx.bv_val(1ull, m_nbit));
            Z3_inc_ref(m_ctx, so);
            Z3_solver_assert(m_ctx, m_solver, so);
            Z3_dec_ref(m_ctx, so);
            v_model.reserve(20);
        }

        inline bool check() { 
            m_lbool = Z3_solver_check(m_ctx, m_solver);
            return m_lbool == Z3_L_TRUE;
        }

        inline void operator++()
        {
            Z3_ast eq = Z3_mk_eq(m_ctx, m_addr, last_avoid_addr);
            Z3_inc_ref(m_ctx, eq);
            Z3_ast neq = Z3_mk_not(m_ctx, eq);
            Z3_inc_ref(m_ctx, neq);
            Z3_solver_assert(m_ctx, m_solver, neq);
            Z3_dec_ref(m_ctx, eq);
            Z3_dec_ref(m_ctx, neq);
            Z3_dec_ref(m_ctx, last_avoid_addr);
        }

        inline operator Z3_ast() { return m_addr; }

        inline Vns operator*()
        {
            Z3_model m_model = Z3_solver_get_model(m_ctx, m_solver); vassert(m_model);
            Z3_model_inc_ref(m_ctx, m_model);
            v_model.emplace_back(m_model);
            Z3_ast r = 0;
            bool status = Z3_model_eval(m_ctx, m_model, m_addr, /*model_completion*/false, &r);
            Z3_inc_ref(m_ctx, r);
            last_avoid_addr = r;
            Z3_ast_kind rkind = Z3_get_ast_kind(m_ctx, r);
            if (rkind != Z3_NUMERAL_AST) { 
                vassert(0); 
            }
            return Vns(m_ctx, r, m_nbit);
        }
        inline ~Itaddress() {
            Z3_dec_ref(m_ctx, m_addr);
            if ((context*)(&m_ctx) != nullptr) {
                m_solver.pop();
                for (auto m : v_model) Z3_model_dec_ref(m_ctx, m);
            }
        }
    };
private:
    std::hash_map<ADDR, Register<0x1000>*> mem_change_map;
    Bool need_record;

public:
    PML4T **CR3;
    UInt user;
    Z3_context m_ctx;
    State &m_state;
    MEM(State& so, context* ctx, Bool _need_record);
    MEM(State& so, MEM& father_mem, context* ctx, Bool _need_record);
    ~MEM();

    ULong map(ULong address, ULong length);
    void copy(MEM& mem);
    ULong unmap(ULong address, ULong length);

    void write_bytes(ULong address, ULong length, UChar* data);

    inline void set_double_page(ADDR address, Pap &addrlst) {
        addrlst.guest_addr = address;
        addrlst.Surplus = 0x1000 - (address & 0xfff);
        addrlst.t_page_addr = (UChar*)GETPAGE((ULong)address)->unit->m_bytes + (address & 0xfff);
    }

    inline UChar* get_next_page(ADDR address) {
        return (UChar*)GETPAGE((ULong)(address + 0x1000))->unit->m_bytes;
    }

    inline PAGE* getMemPage(register ADDR address) {
        return GETPAGE((ULong)address);
    }

    Itaddress addr_begin(solver& s, Z3_ast addr) { return Itaddress(s, addr); }

    private:
        Vns _Iex_Load_a(PAGE* P, ADDR address, UShort size) {
            PAGE* nP = getMemPage(address + 0x1000);
            UInt plength = 0x1000 - ((UShort)address & 0xfff);
            return nP->unit->Iex_Get(0, size - plength).translate(m_ctx).Concat(P->unit->Iex_Get(((UShort)address & 0xfff), plength));
        }

        Vns _Iex_Load_b(PAGE* P, ADDR address, UShort size) {
            PAGE* nP = getMemPage(address + 0x1000);
            UInt plength = 0x1000 - ((UShort)address & 0xfff);
            return nP->unit->Iex_Get(0, size - plength).translate(m_ctx).Concat(P->unit->Iex_Get(((UShort)address & 0xfff), plength, m_ctx));
        }
    template<IRType ty>
    Vns ReZero() {
        switch (ty) {
        case 8:
        case Ity_I8:  return Vns(m_ctx, (UChar)0);
        case 16:
        case Ity_I16: {return Vns(m_ctx, (UShort)0);}
        case 32:
        case Ity_F32:
        case Ity_I32: {return Vns(m_ctx, (UInt)0); }
        case 64:
        case Ity_F64:
        case Ity_I64: {return Vns(m_ctx, (ULong)0); }
        case 128:
        case Ity_I128:
        case Ity_V128: {return Vns(m_ctx,  _mm_setzero_si128()); }
        case 256:
        case Ity_V256: {return Vns(m_ctx, _mm256_setzero_si256()); }
        default:vpanic("error IRType");
        }
    }

    public:
    // ty  IRType || n_bits
    template<IRType ty>
    inline Vns Iex_Load(ADDR address)
    {
        PAGE *P = getMemPage(address);
        UShort offset = (UShort)address & 0xfff;
        UShort size;
        if (P->user == -1ull) {
            return ReZero<ty>();
        }
        if (user == P->user) {//WNC
            switch (ty) {
            case 8:
            case Ity_I8:  return P->unit->Iex_Get<Ity_I8>(offset);
            case 16:
            case Ity_I16: { 
                if (offset >= 0xfff) { return _Iex_Load_a(P, address, 2); }return P->unit->Iex_Get<Ity_I16>(offset);
            }
            case 32:
            case Ity_F32:
            case Ity_I32: { 
                if (offset >= 0xffd) { return _Iex_Load_a(P, address, 4); }return P->unit->Iex_Get<Ity_I32>(offset);
            }
            case 64:
            case Ity_F64:
            case Ity_I64: { 
                if (offset >= 0xff9) { return _Iex_Load_a(P, address, 8); }return P->unit->Iex_Get<Ity_I64>(offset);
            }
            case 128:
            case Ity_I128:
            case Ity_V128: { 
                if (offset >= 0xff1) { return _Iex_Load_a(P, address, 16); }return P->unit->Iex_Get<Ity_V128>(offset);
            }
            case 256:
            case Ity_V256: { 
                if (offset >= 0xfe1) { return _Iex_Load_a(P, address, 32); }return P->unit->Iex_Get<Ity_V256>(offset);
            }
            default:vpanic("error IRType");
            }
        }
        else {
            switch (ty) {
            case 8:
            case Ity_I8: {
                return P->unit->Iex_Get<Ity_I8 >(offset, m_ctx);
            }
            case 16:													
            case Ity_I16: {
                if (offset >= 0xfff) { return _Iex_Load_b(P, address, 2); }; return P->unit->Iex_Get<Ity_I16>(offset, m_ctx);
            }
            case 32:
            case Ity_F32:
            case Ity_I32: {
                if (offset >= 0xffd) { return _Iex_Load_b(P, address, 4); }; return P->unit->Iex_Get<Ity_I32>(offset, m_ctx); 
            }
            case 64:
            case Ity_F64:
            case Ity_I64: {
                if (offset >= 0xff9) { return _Iex_Load_b(P, address, 8); }; return P->unit->Iex_Get<Ity_I64>(offset, m_ctx);
            }
            case 128:
            case Ity_I128:
            case Ity_V128: {
                if (offset >= 0xff1) { return _Iex_Load_b(P, address, 16); }; return P->unit->Iex_Get<Ity_V128>(offset, m_ctx);
            }
            case 256:
            case Ity_V256: {
                if (offset >= 0xfe1) { return _Iex_Load_b(P, address, 32); }; return P->unit->Iex_Get<Ity_V256>(offset, m_ctx); 
            }
            default:vpanic("error IRType");
            }
        }
    }

    Vns Iex_Load(ADDR address, IRType ty);

    template<IRType ty>
    Vns Iex_Load(Z3_ast address) {
        addressingMode am(expr(m_state.m_ctx, address));
        Z3_ast reast;
        auto kind = am.analysis_kind();
        if (kind != addressingMode::cant_analysis) {
#ifdef TRACE_AM
            printf("addr: %p  Iex_Load  base: %p {\n", m_state.get_cpu_ip(), am.getBase());
            am.print();
            printf("}\n");
#endif
            reast = m_state.idx2Value(am.getBase(), am.getoffset());
            if (reast) {
                return Vns(m_ctx, reast, no_inc{});
            }
            else {
                if (kind == addressingMode::support_bit_blast) {
                    for (auto offset : am) {
                        Vns data = Iex_Load<ty>(am.getBase() + offset);
                        if (!reast) {
                            reast = data;
                            Z3_inc_ref(m_ctx, reast);
                            continue;
                        }
                        auto eq = Z3_mk_eq(m_ctx, am.getoffset(), Vns(m_ctx, (ADDR)offset));
                        Z3_inc_ref(m_ctx, eq);
                        auto ift = Z3_mk_ite(m_ctx, eq, data, reast);
                        Z3_inc_ref(m_ctx, ift);
                        Z3_dec_ref(m_ctx, reast);
                        Z3_dec_ref(m_ctx, eq);
                        reast = ift;
                    }
                    return Vns(m_ctx, reast, no_inc{});
                }
            }
        }
#ifdef TRACE_AM
        vex_printf("Iex_Load : guest: %p \n", m_state.guest_start);
#endif
        Itaddress it = this->addr_begin(m_state.solv, address);
        uint64_t Z3_RE;
        while (it.check()) {
            auto addr = *it;
            if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
            Vns data = Iex_Load<ty>(Z3_RE);
            if (reast) {
                auto eq = Z3_mk_eq(m_ctx, it, addr);
                Z3_inc_ref(m_ctx, eq);
                auto ift = Z3_mk_ite(m_ctx, eq, data, reast);
                Z3_inc_ref(m_ctx, ift);
                Z3_dec_ref(m_ctx, reast);
                Z3_dec_ref(m_ctx, eq);
                reast = ift;
            }
            else {
                reast = data;
                Z3_inc_ref(m_ctx, reast);
            }
            it++;
        };
        return Vns(m_ctx, reast, no_inc{});
    }

    Vns Iex_Load(Z3_ast address, IRType ty);

    template<IRType ty>
    inline Vns Iex_Load(Vns const &address) {
        if (address.real()) {
            return Iex_Load<ty>((ADDR)address);
        }
        else {
            return Iex_Load<ty>((Z3_ast)address);
        }
    }


    inline Vns Iex_Load(Vns const &address, IRType ty)
    {
        if (address.real()) {
            return Iex_Load((ADDR)address, ty);
        }
        else {
            return Iex_Load((Z3_ast)address, ty);
        }
    }



    template<typename DataTy>
    void Ist_Store(ADDR address, DataTy data) {
        ADDR delta = address - m_state.guest_start_of_block;
        if (delta > 0 && delta < m_state.pap.delta) {
            if (m_state.status == Running) {
                vex_printf("\n********* code: %p has been patched!! *********\n", address);
            }
            m_state.is_dynamic_block = true;
        }
        PAGE* P = getMemPage(address);
        CheckSelf(P, address);
        UShort offset = address & 0xfff;
        if (fastalignD1[sizeof(data) << 3] > 0xFFF - offset) {
            PAGE* nP = getMemPage(address + 0x1000);
            CheckSelf(nP, address + 0x1000);
            UInt plength = (0x1000 - offset);
            P->unit->Ist_Put(offset, (void*)&data, plength);
            nP->unit->Ist_Put(0, ((UChar*)((void*)&data)) + plength, (sizeof(data) - plength));
        }
        else {
            P->unit->Ist_Put(offset, data);
        }
    }

    template<unsigned int bitn>
    void Ist_Store(ADDR address, Z3_ast data) {
        ADDR delta = address - m_state.guest_start_of_block;
        if (delta > 0 && delta < m_state.pap.delta) {
            if (m_state.status == Running) {
                vex_printf("\n********* code: %p has been patched!! refresh the block *********\n", address);
            }
            m_state.is_dynamic_block = true;
        }
        PAGE* P = getMemPage(address);
        CheckSelf(P, address);
        UShort offset = address & 0xfff;
        if (fastalignD1[bitn] > 0xFFF - offset) {
            PAGE* nP = getMemPage(address + 0x1000);
            CheckSelf(nP, address + 0x1000);
            UInt plength = (0x1000 - offset);
            Z3_ast Low = Z3_mk_extract(m_ctx, (plength << 3) - 1, 0, data);
            Z3_inc_ref(m_ctx, Low);
            Z3_ast HI = Z3_mk_extract(m_ctx, bitn - 1, plength << 3, data);
            Z3_inc_ref(m_ctx, HI);
            nP->unit->Ist_Put(offset, Low, plength);
            nP->unit->Ist_Put(0, HI, (bitn >> 3) - plength);
            Z3_dec_ref(m_ctx, Low);
            Z3_dec_ref(m_ctx, HI);
        }
        else {
            P->unit->Ist_Put<bitn>(offset, data);
        }
    }

    template<typename DataTy>
    void Ist_Store(Z3_ast address, DataTy data) {
        uint64_t Z3_RE;
        bool suspend_solve = true;
        LARGE_INTEGER   freq = { 0 };
        LARGE_INTEGER   beginPerformanceCount = { 0 };
        LARGE_INTEGER   closePerformanceCount = { 0 };
        QueryPerformanceFrequency(&freq);
        QueryPerformanceCounter(&beginPerformanceCount);
    redo:
        Itaddress it = this->addr_begin(m_state.solv, address);
        while (it.check()) {
            if (suspend_solve) {
                QueryPerformanceCounter(&closePerformanceCount);
                double delta_seconds = (double)(closePerformanceCount.QuadPart - beginPerformanceCount.QuadPart) / freq.QuadPart;
                if (delta_seconds > 0.01d) {
                    break;
                }
                else {
                    suspend_solve = false;
                }
            }
            auto addr = *it;
            if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
            auto oData = Iex_Load<(IRType)(sizeof(DataTy) << 3)>(Z3_RE);
            auto eq = Z3_mk_eq(m_ctx, it, addr);
            Z3_inc_ref(m_ctx, eq);
            auto n_Data = Z3_mk_ite(m_ctx, eq, Vns(m_ctx, data), oData);
            Z3_inc_ref(m_ctx, n_Data);
            Ist_Store<(IRType)(sizeof(DataTy) << 3)>(Z3_RE, n_Data);
            Z3_dec_ref(m_ctx, n_Data);
            Z3_dec_ref(m_ctx, eq);
            it++;
        }
        if (suspend_solve) {
            addressingMode am(expr(m_state.m_ctx, address));
            auto kind = am.analysis_kind();
            if (kind == addressingMode::support_bit_blast) {
#ifdef TRACE_AM
                printf("addr: %p  Ist_Store base: %p {\n", m_state.get_cpu_ip(), am.getBase());
                am.print();
                printf("}\n");
#endif
                for (auto offset : am) {
                    ADDR raddr = am.getBase() + offset;
                    auto oData = Iex_Load<(IRType)(sizeof(DataTy) << 3)>(raddr);
                    auto eq = Z3_mk_eq(m_ctx, am.getoffset(), Vns(m_ctx, offset));
                    Z3_inc_ref(m_ctx, eq);
                    auto n_Data = Z3_mk_ite(m_ctx, eq, Vns(m_ctx, data), oData);
                    Z3_inc_ref(m_ctx, n_Data);
                    Ist_Store<(IRType)(sizeof(DataTy) << 3)>(raddr, n_Data);
                    Z3_dec_ref(m_ctx, n_Data);
                    Z3_dec_ref(m_ctx, eq);
                }
            }
            else {
                suspend_solve = false;
                it.~Itaddress();
                goto redo;
            }
        }
    }

    //n_bit
    template<unsigned int bitn>
    void Ist_Store(Z3_ast address, Z3_ast data) {
        uint64_t Z3_RE;
        bool suspend_solve = true;
        LARGE_INTEGER   freq = { 0 };
        LARGE_INTEGER   beginPerformanceCount = { 0 };
        LARGE_INTEGER   closePerformanceCount = { 0 };
        QueryPerformanceFrequency(&freq);
        QueryPerformanceCounter(&beginPerformanceCount);
    redo:
        Itaddress it = this->addr_begin(m_state.solv, address);
        while (it.check()) {
            if (suspend_solve) {
                QueryPerformanceCounter(&closePerformanceCount);
                double delta_seconds = (double)(closePerformanceCount.QuadPart - beginPerformanceCount.QuadPart) / freq.QuadPart;
                if (delta_seconds > 0.01d) {
                    break;
                }
                else {
                    suspend_solve = false;
                }
            }
            auto addr = *it;
            if (!Z3_get_numeral_uint64(m_ctx, addr, &Z3_RE)) vassert(0);
            auto oData = Iex_Load<(IRType)bitn>(Z3_RE); 
            auto eq = Z3_mk_eq(m_ctx, it, addr);
            Z3_inc_ref(m_ctx, eq);
            auto n_Data = Z3_mk_ite(m_ctx, eq, data, oData);
            Z3_inc_ref(m_ctx, n_Data);
            Ist_Store<(IRType)bitn>(Z3_RE, n_Data);
            Z3_dec_ref(m_ctx, n_Data);
            Z3_dec_ref(m_ctx, eq);
            it++;
        }
        if (suspend_solve) {
            addressingMode am(expr(m_state.m_ctx, address));
            auto kind = am.analysis_kind();
            if (kind == addressingMode::support_bit_blast) {
#ifdef TRACE_AM
                printf("addr: %p  Ist_Store base: %p {\n", m_state.get_cpu_ip(), am.getBase());
                am.print();
                printf("}\n");
#endif
                for (auto offset : am) {
                    ADDR raddr = am.getBase() + offset;
                    auto oData = Iex_Load<(IRType)bitn>(raddr);
                    auto eq = Z3_mk_eq(m_ctx, am.getoffset(), Vns(m_ctx, offset));
                    Z3_inc_ref(m_ctx, eq);
                    auto n_Data = Z3_mk_ite(m_ctx, eq, data, oData);
                    Z3_inc_ref(m_ctx, n_Data);
                    Ist_Store<(IRType)bitn>(raddr, n_Data);
                    Z3_dec_ref(m_ctx, n_Data);
                    Z3_dec_ref(m_ctx, eq);
                }
            }
            else {
                suspend_solve = false;
                it.~Itaddress();
                goto redo;
            }
        }
    }


    inline void Ist_Store(ADDR address, Vns const &data) {
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
    inline void Ist_Store(Vns const &address, DataTy data) {
        if (address.real()) {
            Ist_Store((ADDR)address, data);
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
            Ist_Store((ADDR)address, data);
        }
        else {
            Ist_Store((Z3_ast)address, data);
        }
    }

    inline operator Z3_context() { return m_ctx; }

private:
    void CheckSelf(PAGE*& P, ADDR address);

    template<>
    inline void Ist_Store(ADDR address, Vns data) = delete;
    template<>
    inline void Ist_Store(ADDR address, Vns &data) = delete;
    template<>
    inline void Ist_Store(ADDR address, Vns const &data) = delete;
    template<>
    inline void Ist_Store(ADDR address, Z3_ast data) = delete;
    template<>
    inline void Ist_Store(ADDR address, Z3_ast &data) = delete;

    template<>
    inline void Ist_Store(Z3_ast address, Vns data) = delete;
    template<>
    inline void Ist_Store(Z3_ast address, Vns &data) = delete;
    template<>
    inline void Ist_Store(Z3_ast address, Vns const &data) = delete;

};

#ifndef UNDEFMEM
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
#endif

#endif //  MEMORY_DEFS_H
