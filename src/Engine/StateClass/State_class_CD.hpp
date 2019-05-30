
#ifndef State_class_defs
#define State_class_defs


typedef struct ChangeView {
	State *elders;
	ChangeView *front;
}ChangeView;

typedef ULong(*Function6)(ULong, ULong, ULong, ULong, ULong, ULong);
typedef ULong(*Function5)(ULong, ULong, ULong, ULong, ULong);
typedef ULong(*Function4)(ULong, ULong, ULong, ULong);
typedef ULong(*Function3)(ULong, ULong, ULong);
typedef ULong(*Function2)(ULong, ULong);
typedef ULong(*Function1)(ULong);

typedef Vns (*Z3_Function6)(Vns &, Vns &, Vns &, Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function5)(Vns &, Vns &, Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function4)(Vns &, Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function3)(Vns &, Vns &, Vns &);
typedef Vns (*Z3_Function2)(Vns &, Vns &);
typedef Vns (*Z3_Function1)(Vns &);


static std::mutex global_state_mutex;
static Bool TriggerBug_is_init = False;

class State {
private:
	Addr64 guest_start_ep;
	Addr64 guest_start;
	void *VexGuestARCHState;

public:
	z3::context m_ctx;
	z3::solver solv;
	std::queue< std::function<void()> > check_stack;
	Long delta;
	std::mutex unit_lock;
	PyObject *base;

protected:
	Bool need_record;

private:
	Pap pap;

	VexTranslateResult res;
	VexRegisterUpdates pxControl = VexRegUpd_INVALID;
	VexArchInfo         vai_guest, vai_host;
	VexGuestExtents     vge;
	VexTranslateArgs    vta;
	VexTranslateResult  vtr;
	VexAbiInfo	        vbi;
	VexControl          vc;

	std::vector<Vns> asserts;
	UShort t_index;

	inline Bool treeCompress(z3::context &ctx, Addr64 Target_Addr, State_Tag Target_Tag, std::vector<State_Tag> &avoid, ChangeView& change_view, std::hash_map<ULong, Vns> &change_map, std::hash_map<UShort, Vns> &regs_change_map);
	
public:
	Register<1000> regs;
	MEM mem;//多线程设置相同user，不同state设置不同user
	ULong runed = 0;
	std::vector <State*> branch;
	State_Tag status;




	State(char *filename, Addr64 gse, Bool ) ;
	State(State *father_state, Addr64 gse) ;

	~State() ;
	void thread_register();
	void thread_unregister();
	void IR_init();
	inline IRSB* BB2IR();
	inline void add_assert(Vns &assert, Bool ToF);
	inline void add_assert_eq(Vns &eqA, Vns &eqB);
	void start(Bool first_bkp_pass);
	void compress(Addr64 Target_Addr, State_Tag Target_Tag, std::vector<State_Tag> &avoid);//最大化缩合状态 
	inline Vns getassert(z3::context &ctx);
	inline Addr64 get_guest_start();
	inline Addr64 get_guest_start_ep();
	inline Vns tIRExpr(IRExpr*);
	inline void write_regs(int offset, void*, int length);
	inline void read_regs(int offset, void*, int length);

	inline Vns CCall(IRCallee *cee, IRExpr **exp_args, IRType ty);
	void read_mem_dump(const char *);
	PAGE* getMemPage(Addr64 addr);
	inline Vns T_Unop(IROp, IRExpr*);
	inline Vns T_Binop(IROp, IRExpr*, IRExpr*);
	inline Vns T_Triop(IROp, IRExpr*, IRExpr*, IRExpr*);
	inline Vns T_Qop(IROp, IRExpr*, IRExpr*, IRExpr*, IRExpr*);
	inline Vns ILGop(IRLoadG *lg);

	inline operator context&();
	inline operator Z3_context();
	inline operator std::string();
};

#endif