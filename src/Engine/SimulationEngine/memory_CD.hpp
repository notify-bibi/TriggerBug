#ifndef MEMORY_DEFS_H
#define MEMORY_DEFS_H


extern UInt global_user;

typedef struct PAGE {
	ULong user;
	UInt used_point;
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


class MEM{
	friend class State;
private:
	std::hash_map<Addr64, Register<0x1000>*> mem_change_map;
	Bool need_record;
public:
	PML4T **CR3;
	UInt user;
	Z3_context m_ctx;
	solver *m_solv; 
	inline MEM(solver *, context * ctx,Bool _need_record);
	inline MEM(solver *, MEM &, context * ctx, Bool _need_record);
	inline ~MEM();
	inline void freeMap();
	ULong map(ULong, ULong);
	void copy(MEM &);
	ULong unmap(ULong, ULong );
	inline void write_bytes(ULong , ULong , unsigned char *);
	inline void set_double_page(Addr64 , Pap &);
	inline PAGE* getMemPage(Addr64);

	template<IRType ty>
	inline Vns Iex_Load(Addr64);	// ir<-mem
	inline Vns Iex_Load(Addr64, IRType);	// ir<-mem

	template<IRType ty>
	inline Vns Iex_Load(Z3_ast address);// ir<-mem
	inline Vns Iex_Load(Z3_ast address, IRType);// ir<-mem
	template<IRType ty>
	inline Vns Iex_Load(Vns const &);// ir<-mem
	inline Vns Iex_Load(Vns const &, IRType);// ir<-mem

	template<typename DataTy>
	inline void Ist_Store(Addr64 address, DataTy data);// ir->mem
	template<unsigned int bitn>
	inline void MEM::Ist_Store(Addr64 address, Z3_ast data);

	template<typename DataTy>
	inline void Ist_Store(Z3_ast address, DataTy data);// ir->mem
	template<unsigned int bitn>
	inline void MEM::Ist_Store(Z3_ast address, Z3_ast data);



	inline void Ist_Store(Z3_ast, Vns const &);// ir->mem
	inline void Ist_Store(Addr64, Vns const &);// ir->mem
	template<typename DataTy>
	inline void Ist_Store(Vns const &, DataTy);// ir->mem
	inline void Ist_Store(Vns const &, Vns const &);// ir->mem

	inline operator Z3_context() { return m_ctx; }

private:
	inline void CheckSelf(PAGE *&P, Addr64 address);
	template<>
	inline void Ist_Store(Addr64 address, Vns data) = delete;
	template<>
	inline void Ist_Store(Addr64 address, Vns &data) = delete;
	template<>
	inline void Ist_Store(Addr64 address, Vns const &data) = delete;
	template<>
	inline void Ist_Store(Addr64 address, Z3_ast data) = delete;
	template<>
	inline void Ist_Store(Addr64 address, Z3_ast &data) = delete;

	template<>
	inline void Ist_Store(Z3_ast address, Vns data) = delete;
	template<>
	inline void Ist_Store(Z3_ast address, Vns &data) = delete;
	template<>
	inline void Ist_Store(Z3_ast address, Vns const &data) = delete;

}; 


#endif //  MEMORY_DEFS_H