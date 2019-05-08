#include <iostream>
#include <sstream>
#include <tuple>
#include <exception>
#include <string>
#include <vector>
#define _SILENCE_STDEXT_HASH_DEPRECATION_WARNINGS
#include <hash_map>;

#include "../Z3_Target_Call/Z3_Target_Call.hpp"

UChar arch_bitn = 64;

extern Variable ir_temp[MAX_THREADS][400];
extern std::hash_map<Addr64, Hook_struct> CallBackDict;
extern State_Tag(*Ijk_call_back)(State *, IRJumpKind);
extern ThreadPool *pool;
extern void* funcDict(void*);
extern tinyxml2::XMLDocument doc;

std::string replace(const char *pszSrc, const char *pszOld, const char *pszNew)
{
	std::string strContent, strTemp;
	strContent.assign(pszSrc);
	std::string::size_type nPos = 0;
	while (true)
	{
		nPos = strContent.find(pszOld, nPos);
		strTemp = strContent.substr(nPos + strlen(pszOld), strContent.length());
		if (nPos == std::string::npos)
		{
			break;
		}
		strContent.replace(nPos, strContent.length(), pszNew);
		strContent.append(strTemp);
		nPos += strlen(pszNew) - strlen(pszOld) + 1; //防止重复替换 避免死循环
	}
	return strContent;
}



inline unsigned int eval_all(std::vector<Z3_ast> &result, solver &solv, Z3_ast nia) {
	//std::cout << nia << std::endl;
	//std::cout << state.solv.assertions() << std::endl;
	result.reserve(100);
	solv.push();
	std::vector<Z3_model> mv;
	mv.reserve(20);
	register Z3_context ctx = solv.ctx();
	for (int nway = 0; ; nway++) {
		Z3_lbool b;
		try {
			/*auto err = Z3_ast_to_string(ctx, nia);
			delete err;*/
			b = Z3_solver_check(ctx, solv);
		}
		catch (...) {
			Z3_error_code e = Z3_get_error_code(ctx);
			if (e != Z3_OK )
				throw (Z3_get_error_msg(ctx, e));
			throw e;
		}
		if (b == Z3_L_TRUE) {
			Z3_model m_model = Z3_solver_get_model(ctx, solv);
			Z3_model_inc_ref(ctx, m_model);
			mv.emplace_back(m_model);
			Z3_ast r = 0;
			bool status = Z3_model_eval(ctx, m_model, nia, /*model_completion*/false, &r);
			Z3_inc_ref(ctx, r);
			result.emplace_back(r);
			Z3_ast_kind rkind = Z3_get_ast_kind(ctx, r);
			if (rkind != Z3_NUMERAL_AST) {
				std::cout << rkind << Z3_ast_to_string(ctx, nia)  << std::endl;
				std::cout << solv.assertions() << std::endl;
				vassert(0);
			}
			Z3_ast eq = Z3_mk_eq(ctx, nia, r);
			Z3_inc_ref(ctx, eq);
			Z3_ast neq = Z3_mk_not(ctx, eq);
			Z3_inc_ref(ctx, neq);
			Z3_solver_assert(ctx, solv, neq);
			Z3_dec_ref(ctx, eq);
			Z3_dec_ref(ctx, neq);
		}
		else {
#if defined(OPSTR)
			//std::cout << "     sizeof symbolic : " << result.size() ;
			for (auto s : result) std::cout << ", " << Z3_ast_to_string(ctx, s);
#endif
			solv.pop();
			for (auto m : mv) Z3_model_dec_ref(ctx, m);

			return result.size();
		}
	}
}

Addr64 traceIrAddrress;
int traceJmp;
int traceState;

State::State(char *filename, Addr64 gse, Bool _need_record) :
	m_ctx(), 
	mem(&solv, &m_ctx,need_record),
	regs(m_ctx, need_record), 
	solv(m_ctx), need_record(_need_record),
	status(NewState),
	VexGuestARCHState(NULL),
	delta(0)
{
	Func_Map_Init();
	doc.LoadFile(filename);
	auto doc_TriggerBug = doc.FirstChildElement("TriggerBug");
	sscanf(doc_TriggerBug->FirstChildElement("VexArch")->GetText(), "%x", &guest);
	int Thread_num;
	doc_TriggerBug->FirstChildElement("MaxThreadsNum")->QueryIntText((Int*)(&Thread_num));
	assert(Thread_num <= MAX_THREADS);
	if (pool) 
		delete pool;
	pool = new ThreadPool(Thread_num);

	asserts.resize(5);
	branch.reserve(10);
	init_threads_id(); 
	tempmeminit(); 
	IR_init(); 
	init_tebles();
	read_mem_dump(doc_TriggerBug->FirstChildElement("MemoryDumpPath")->GetText());
	if (gse)
		guest_start_ep = gse;
	else {
		if (doc_TriggerBug->FirstChildElement("GuestStartAddress")) {
			sscanf(doc_TriggerBug->FirstChildElement("GuestStartAddress")->GetText(), "%llx", &guest_start_ep);
		}
		else {
			Int offset;
			doc_TriggerBug->FirstChildElement("RegsIpOffset")->QueryIntText(&offset);
			guest_start_ep = regs.Iex_Get(offset,Ity_I64);
		}
	}
	guest_start = guest_start_ep;

	sscanf(doc_TriggerBug->FirstChildElement("DEBUG")->FirstChildElement("TraceIrAddrress")->GetText(), "%llx", &traceIrAddrress);
	doc_TriggerBug->FirstChildElement("DEBUG")->FirstChildElement("TraceState")->QueryIntText(&traceState);
	doc_TriggerBug->FirstChildElement("DEBUG")->FirstChildElement("TraceJmp")->QueryIntText(&traceJmp);

};
State::State(State *father_state, Addr64 gse) :
	m_ctx(),
	mem(&solv, father_state->mem, &m_ctx, need_record), 
	guest_start_ep(gse),
	guest_start(guest_start_ep), 
	solv(m_ctx, father_state->solv,  z3::solver::translate{}),
	regs(father_state->regs, m_ctx, need_record),
	need_record(father_state->need_record),
	status(NewState),
	VexGuestARCHState(NULL),
	delta(0)
{
	IR_init();
};

State::~State() { 
	unregister_tid(GetCurrentThreadId());
	if (VexGuestARCHState) delete VexGuestARCHState;
	for (auto s : branch) delete s;
}
	
PAGE* State::getMemPage(Addr64 addr) { return mem.getMemPage(addr); };
	
inline State::operator context&() { return m_ctx; }
inline State::operator Z3_context() { return m_ctx; }
inline State::operator std::string(){
    std::string str;
    char hex[20];
    std::string strContent;
    

    str.append("\n#entry:");
    snprintf(hex, sizeof(hex),  "%llx", guest_start_ep);
    strContent.assign(hex);
    str.append(strContent);
    str.append(" end:");
    snprintf(hex, sizeof(hex),  "%llx ", guest_start);
    strContent.assign(hex);
    str.append(strContent);

    switch (status) {
	case NewState:str.append("NewState "); break;
    case Running:str.append("Running "); break;
    case Fork:str.append("Fork "); break;
    case Death:str.append("Death "); break;
	default:
		snprintf(hex, sizeof(hex),  "%d ", status);
		strContent.assign(hex);
		str.append(strContent); break;
    }

    str.append(" #child{\n");
    if (branch.empty()) {
        switch (status) {
		case NewState:str.append("NewState "); break;
        case Running:str.append("Running "); break;
        case Fork:str.append("Fork "); break;
        case Death:str.append("Death "); break;
		default:
			snprintf(hex, sizeof(hex),  "%d ", status);
			strContent.assign(hex);
			str.append(strContent); break;
        }
        snprintf(hex, sizeof(hex),  "%llx    \n}\n ", guest_start_ep);
        strContent.assign(hex);
        str.append(strContent);
        return str;
    }
    else {
        for (auto state : branch) {
            std::string child = *state;
            str.append(replace(child.c_str(), "\n", "\n   >"));
        }
    }
    str.append("\n}\n");
    
    
    return str;
}

inline expr State::getassert(z3::context &ctx) {
	if (asserts.empty()) {
		vpanic("impossible assertions num is zero");
	}
	auto it = asserts.begin();
	auto end = asserts.end();
	auto result = *it;
	it ++;
	while (it != end) {
		result = result && *it;
		it ++;
	}
	return result.translate(ctx).simplify();
}
inline Addr64 State::get_guest_start()
{
	return guest_start;
}
inline Addr64 State::get_guest_start_ep()
{
	return guest_start_ep;
}
inline std::ostream & operator<<(std::ostream & out, State & n) {
    return out<< (std::string)n;
}


inline IRSB* State::BB2IR() {
	mem.set_double_page(guest_start, pap);
	pap.start_swap       = 0;
	vta.guest_bytes      = (UChar *)(pap.t_page_addr);
	vta.guest_bytes_addr = (Addr64)(guest_start);
	vta.traceflags       = NULL;
	//vta.traceflags = VEX_TRACE_FE;
	vta.pap = &pap;
	IRSB *irsb;
	if(0){
		printf("GUESTADDR %16llx   RUND:%ld CODES   ", guest_start, runed);
		TESTCODE(
			irsb = LibVEX_FrontEnd(&vta, &res, &pxControl);
		);
	}
	else {
		return LibVEX_FrontEnd(&vta, &res, &pxControl);
	}
	return irsb;
}




inline void State::add_assert(Variable & assert,Bool ToF)
{
	assert = assert.simplify();
	if(assert.is_bool()){
		if (ToF) {
			Z3_solver_assert(m_ctx, solv, assert);
			asserts.push_back(assert);
		}
		else {
			auto not = !assert;
			Z3_solver_assert(m_ctx, solv, not);
			asserts.push_back(not);
		}
	}
	else {
		auto ass = (assert == 1);
		Z3_solver_assert(m_ctx, solv, ass);
		asserts.push_back(ass);
	}
}

inline void State::add_assert_eq(Variable & eqA, Variable & eqB)
{
	Variable ass = (eqA == eqB).simplify();
	Z3_solver_assert(m_ctx, solv, ass);
	solv.add(ass);
	asserts.push_back(ass);
}

inline void State::write_regs(int offset, void* addr, int length) { regs.write_regs(offset, addr, length); }
inline void State::read_regs(int offset, void* addr, int length) { regs.read_regs(offset, addr, length); }


inline Variable State::CCall(IRCallee *cee, IRExpr **exp_args, IRType ty)
{
	Int regparms = cee->regparms;
	UInt mcx_mask = cee->mcx_mask;
	Bool z3_mode = False;

	Variable arg0 = tIRExpr(exp_args[0]);
	if (arg0.symbolic()) z3_mode = True;
	if (!exp_args[1]) return (z3_mode) ? ((Z3_Function1)(funcDict(cee->addr)))(arg0) : Variable(((Function1)(cee->addr))(arg0), m_ctx);
	Variable arg1 = tIRExpr(exp_args[1]);
	if (arg1.symbolic()) z3_mode = True;
	if (!exp_args[2]) return (z3_mode) ? ((Z3_Function2)(funcDict(cee->addr)))(arg0, arg1) : Variable(((Function2)(cee->addr))(arg0, arg1), m_ctx);
	Variable arg2 = tIRExpr(exp_args[2]);
	if (arg2.symbolic()) z3_mode = True;
	if (!exp_args[3]) return (z3_mode) ? ((Z3_Function3)(funcDict(cee->addr)))(arg0, arg1, arg2) : Variable(((Function3)(cee->addr))(arg0, arg1, arg2), m_ctx);
	Variable arg3 = tIRExpr(exp_args[3]);
	if (arg3.symbolic()) z3_mode = True;
	if (!exp_args[4]) return (z3_mode) ? ((Z3_Function4)(funcDict(cee->addr)))(arg0, arg1, arg2, arg3) : Variable(((Function4)(cee->addr))(arg0, arg1, arg2, arg3), m_ctx);
	Variable arg4 = tIRExpr(exp_args[4]);
	if (arg4.symbolic()) z3_mode = True;
	if (!exp_args[5]) return (z3_mode) ? ((Z3_Function5)(funcDict(cee->addr)))(arg0, arg1, arg2, arg3, arg4) : Variable(((Function5)(cee->addr))(arg0, arg1, arg2, arg3, arg4), m_ctx);
	Variable arg5 = tIRExpr(exp_args[5]);
	if (arg5.symbolic()) z3_mode = True;
	if (!exp_args[6]) return (z3_mode) ? ((Z3_Function6)(funcDict(cee->addr)))(arg0, arg1, arg2, arg3, arg4, arg5) : Variable(((Function6)(cee->addr))(arg0, arg1, arg2, arg3, arg4, arg5), m_ctx);

}



inline Variable State::tIRExpr(IRExpr* e)
{
	switch (e->tag) {
	case Iex_Get  : { return regs.Iex_Get(e->Iex.Get.offset, e->Iex.Get.ty); }
	case Iex_RdTmp: { return ir_temp[t_index][e->Iex.RdTmp.tmp]; }
	case Iex_Unop : { return T_Unop (e->Iex.Unop.op, e->Iex.Unop.arg); }
	case Iex_Binop: { return T_Binop(e->Iex.Binop.op, e->Iex.Binop.arg1, e->Iex.Binop.arg2); }
	case Iex_Triop: { return T_Triop(e->Iex.Triop.details->op, e->Iex.Triop.details->arg1, e->Iex.Triop.details->arg2, e->Iex.Triop.details->arg3); }
	case Iex_Qop  : { return T_Qop  (e->Iex.Qop.details->op, e->Iex.Qop.details->arg1, e->Iex.Qop.details->arg2, e->Iex.Qop.details->arg3, e->Iex.Qop.details->arg4); }
	case Iex_Load : { return mem.Iex_Load(tIRExpr(e->Iex.Load.addr), e->Iex.Get.ty); }
	case Iex_Const: { return Variable(m_ctx,e->Iex.Const.con); }
	case Iex_ITE  : { Variable cond = tIRExpr(e->Iex.ITE.cond); return (cond.real()) ? ((UChar)cond & 0b1) ? tIRExpr(e->Iex.ITE.iftrue) : tIRExpr(e->Iex.ITE.iffalse) : Variable(m_ctx, Z3_mk_ite(m_ctx, cond == 1, tIRExpr(e->Iex.ITE.iftrue), tIRExpr(e->Iex.ITE.iffalse))); }
	case Iex_CCall: { return CCall(e->Iex.CCall.cee, e->Iex.CCall.args, e->Iex.CCall.retty); }
	case Iex_GetI : { auto ix = tIRExpr(e->Iex.GetI.ix); assert(ix.real()); return regs.Iex_Get(e->Iex.GetI.descr->base + (((UInt)(e->Iex.GetI.bias + (int)(ix))) % e->Iex.GetI.descr->nElems)*ty2length(e->Iex.GetI.descr->elemTy), e->Iex.GetI.descr->elemTy); };
	case Iex_GSPTR: {
		switch (guest) {
		case VexArchAMD64:
			if (!VexGuestARCHState) VexGuestARCHState = new VexGuestAMD64State;
			((VexGuestAMD64State*)VexGuestARCHState)->guest_RAX = regs.Iex_Get(16, Ity_I64);
			((VexGuestAMD64State*)VexGuestARCHState)->guest_RCX = regs.Iex_Get(24, Ity_I64);
			break;
		default:
			vpanic("not support");
		}
		return Variable(VexGuestARCHState, m_ctx, arch_bitn);
	};
	case Iex_VECRET:
	case Iex_Binder:
	default:vpanic("tIRExpr ");
	}
}
Bool chase_into_ok(void *value,Addr addr) {
	std::cout << value << addr << std::endl;
	return True;
}
inline void State::thread_register()
{
	{
		std::unique_lock<std::mutex> lock(global_user_mutex);
		register_tid(GetCurrentThreadId());
	}
	if (traceState)
		std::cout << "\n+++++++++++++++ Thread ID: " << GetCurrentThreadId() << "  address: " << std::hex << guest_start << "  Started +++++++++++++++\n" << std::endl;

	auto i = temp_index();
	for (int j = 0; j < 400; j++) {
		ir_temp[i][j].m_ast = NULL;
	}
}
inline void State::thread_unregister()
{

	if (traceState)
		std::cout << "\n+++++++++++++++ Thread ID: " << GetCurrentThreadId() << "  address: " << std::hex << guest_start << "  OVER +++++++++++++++\n" << std::endl;
	
	auto i = temp_index();
	for (int j = 0; j < 400; j++) {
		ir_temp[i][j].~Variable();
	}
	{
		std::unique_lock<std::mutex> lock(global_user_mutex);
		unregister_tid(GetCurrentThreadId());
	}
}
void State::IR_init() {
	LibVEX_default_VexControl(&vc);
	LibVEX_default_VexArchInfo(&vai_host);
	LibVEX_default_VexArchInfo(&vai_guest);
	LibVEX_default_VexAbiInfo(&vbi);

	auto doc_VexControl = doc.FirstChildElement("TriggerBug")->FirstChildElement("VexControl");

	vbi.guest_amd64_assume_gs_is_const = True;
	vbi.guest_amd64_assume_fs_is_const = True;
	vc.iropt_verbosity = 0;
	doc_VexControl->FirstChildElement("iropt_level")->QueryIntText((Int*)(&vc.iropt_level));
	vc.iropt_unroll_thresh = 0;
	vc.guest_max_insns = 100;    // max instruction
	vc.guest_chase_thresh = 0;

	sscanf(doc_VexControl->FirstChildElement("iropt_register_updates_default")->GetText(), "%x", &vc.iropt_register_updates_default);
	sscanf(doc_VexControl->FirstChildElement("pxControl")->GetText(), "%x", &pxControl);

	vex_hwcaps_vai(HOSTARCH, &vai_host);
	vex_hwcaps_vai(guest, &vai_guest);
	vai_host.endness = VexEndnessLE;//VexEndnessBE
	vai_guest.endness = VexEndnessLE;//VexEndnessBE

	vex_prepare_vbi(guest, &vbi);
	vta.callback_opaque = NULL;
	vta.preamble_function = NULL;
	vta.instrument1 = NULL;
	vta.instrument2 = NULL;
	vta.finaltidy = NULL;
	vta.preamble_function = NULL;

	vta.disp_cp_chain_me_to_slowEP = (void *)dispatch;
	vta.disp_cp_chain_me_to_fastEP = (void *)dispatch;
	vta.disp_cp_xindir = (void *)dispatch;
	vta.disp_cp_xassisted = (void *)dispatch;

	vta.arch_guest = guest;
	vta.archinfo_guest = vai_guest;
	vta.arch_host = HOSTARCH;
	vta.archinfo_host = vai_host;
	vta.abiinfo_both = vbi;
	vta.guest_extents = &vge;
	vta.chase_into_ok = chase_into_ok;
	vta.needs_self_check = needs_self_check;
}

inline void State::init_tebles()
{
	for (int i = 0; i < 257; i++) fastalignD1[i] = (((((i)-1)&-8) + 8) >> 3) - 1;
	for (int i = 0; i < 257; i++) fastalign[i] = (((((i)-1)&-8) + 8) >> 3);
	for (int i = 0; i <= 64; i++) fastMask[i] = (1ull << i) - 1; fastMask[64] = -1ULL;
	for (int i = 0; i <= 64; i++) fastMaskI1[i] = (1ull << (i+1)) - 1; fastMaskI1[63] = -1ULL; fastMaskI1[64] = -1ULL;
	for (int i = 0; i <= 7; i++) fastMaskB[i] = (1ull << (i << 3)) - 1; fastMaskB[8] = -1ULL;
	for (int i = 0; i <= 7; i++) fastMaskBI1[i] = (1ull << ((i+1) << 3)) - 1; fastMaskBI1[7] = -1ULL;
	
	
	for (int i = 0; i <= 64; i++) fastMaskReverse[i] = ~fastMask[i];
	for (int i = 0; i <= 64; i++) fastMaskReverseI1[i] = ~fastMaskI1[i];

	QueryPerformanceFrequency(&freq_global);
	QueryPerformanceCounter(&beginPerformanceCount_global);
	if (vex_initdone) return;
	register_tid(GetCurrentThreadId());
	LibVEX_Init(&failure_exit, &vex_log_bytes, 0/*debuglevel*/, &vc);
	unregister_tid(GetCurrentThreadId());

}
void State::read_mem_dump(const char  *filename)
{
	struct memdump {
		unsigned long long nameoffset;
		unsigned long long address;
		unsigned long long length;
		unsigned long long dataoffset;
	}buf;
	FILE *infile;
	infile = fopen(filename, "rb");
	if (!infile) {
		printf("%s, %s", filename, "not exit/n");
		getchar();
		exit(1);
	}
	unsigned long long length, fp, err, name_start_offset, name_end_offset;
	fread(&length, 8, 1, infile);
	fseek(infile, 24, SEEK_SET);
	name_start_offset = length;
	fread(&name_end_offset, 8, 1, infile);
	length /= 32;
	char *name_buff = (char *)malloc(name_end_offset-name_start_offset);
	fseek(infile, name_start_offset, SEEK_SET);
	fread(name_buff, 1, name_end_offset - name_start_offset, infile);
	fseek(infile, 0, SEEK_SET);
	char *name;
	for (unsigned int segnum = 0; segnum < length; segnum++) {
		fread(&buf, 32, 1, infile);
		unsigned char *data = (unsigned char *)malloc(buf.length);
		fp = ftell(infile);
		fseek(infile, buf.dataoffset, SEEK_SET);
		fread(data, buf.length, 1, infile);
		name = &name_buff[buf.nameoffset - name_start_offset];
		if (GET8(name)== 0x7265747369676572) {
			memcpy((regs.m_bytes + buf.address), data, buf.length);
			memset((regs.m_fastindex + buf.address), 0, buf.length);
		}else {
			printf("name:%18s address:%016llx data offset:%010llx length:%010llx\n", name, buf.address, buf.dataoffset, buf.length);
			if (err = mem.map(buf.address, buf.length))
				printf("warning %s had maped before length: %llx\n", name, err);
			mem.write_bytes(buf.address, buf.length, data);
		}
		fseek(infile, fp, SEEK_SET);
		free(data);
	}
	free(name_buff);
	fclose(infile);
}



void State::start(Bool first_bkp_pass) {
	if (status != NewState) {
		vassert(0);
	}
	Bool NEED_CHECK = False;
	Bool is_first_bkp_pass = False;
	Addr64 hook_bkp = NULL;
	status = Running;
	thread_register();
	t_index=temp_index();
	
	try {
		try {
			if(first_bkp_pass)
				if ((UChar)mem.Iex_Load(Variable(guest_start, m_ctx), Ity_I8) == 0xCC) {
					is_first_bkp_pass = True;
					goto bkp_pass;
				}
			for (;;) {
For_Begin:
				IRSB* irsb = BB2IR();
				if (traceJmp)
					vex_printf("Jmp: %llx \n",guest_start); 

For_Begin_NO_Trans:
				for (UShort i = 0; i < irsb->stmts_used; i++) {
					IRStmt *s = irsb->stmts[i];
					if (guest_start == traceIrAddrress) { NEED_CHECK = True; }
					if(NEED_CHECK) ppIRStmt(s);
					switch (s->tag) {
					case Ist_Put: {regs.Ist_Put(s->Ist.Put.offset, tIRExpr(s->Ist.Put.data)); break; }
					case Ist_Store: {mem.Ist_Store(tIRExpr(s->Ist.Store.addr), tIRExpr(s->Ist.Store.data)); break; }
					case Ist_WrTmp: {ir_temp[t_index][s->Ist.WrTmp.tmp] = tIRExpr(s->Ist.WrTmp.data);
						if (NEED_CHECK)std::cout << ir_temp[t_index][s->Ist.WrTmp.tmp] << std::endl;
						break; 
					}
					case Ist_CAS /*比较和交换*/: {//xchg    rax, [r10]
						IRCAS cas = *(s->Ist.CAS.details);
						Variable addr = tIRExpr(cas.addr);//r10.value
						Variable expdLo = tIRExpr(cas.expdLo);
						Variable dataLo = tIRExpr(cas.dataLo);
						if ((cas.oldHi != IRTemp_INVALID) && (cas.expdHi)) {//double
							Variable expdHi = tIRExpr(cas.expdHi);
							Variable dataHi = tIRExpr(cas.dataHi);
							ir_temp[t_index][cas.oldHi] = mem.Iex_Load(addr, length2ty(expdLo.bitn));
							ir_temp[t_index][cas.oldLo] = mem.Iex_Load(addr, length2ty(expdLo.bitn));
							mem.Ist_Store(addr, dataLo);
							mem.Ist_Store(addr + (dataLo.bitn >> 3), dataHi);
						}
						else {//single
							ir_temp[t_index][cas.oldLo] = mem.Iex_Load(addr, length2ty(expdLo.bitn));
							mem.Ist_Store(addr, dataLo);
						}
						break;
					}
					case Ist_Exit: {
						Variable guard = tIRExpr(s->Ist.Exit.guard);
						if (guard.real()) {
							if ((UChar)guard) { 
								if (s->Ist.Exit.jk != Ijk_Boring
									&& s->Ist.Exit.jk != Ijk_Call
									&& s->Ist.Exit.jk != Ijk_Ret
									) 
								{
									status = Ijk_call_back(this, s->Ist.Exit.jk);
									if (status != Running) {
										goto EXIT;
									}
									if (delta) {
										guest_start = guest_start + delta;
										delta = 0;
										goto For_Begin;
									}
								}
								else {
									guest_start = s->Ist.Exit.dst->Ico.U64;
									hook_bkp = NULL;
									goto For_Begin;
								}
							}
							break;
						}
						else {
							std::vector<Z3_ast> guard_result;
							switch (eval_all(guard_result, solv, guard)) {
							case 0: status = Death; goto EXIT;
							case 1:{
								uint64_t rgurd;
								Z3_get_numeral_uint64(m_ctx, guard_result[0], &rgurd);
								Z3_dec_ref(m_ctx, guard_result[0]);
								if (rgurd&1) {
									if (s->Ist.Exit.jk != Ijk_Boring
										&& s->Ist.Exit.jk != Ijk_Call
										&& s->Ist.Exit.jk != Ijk_Ret
										)
									{
										status = Ijk_call_back(this, s->Ist.Exit.jk);
										if (status != Running) {
											goto EXIT;
										}
										if (delta) {
											guest_start = guest_start + delta;
											delta = 0;
											goto For_Begin;
										}
									}
									else {
										guest_start = s->Ist.Exit.dst->Ico.U64;
										hook_bkp = NULL;
										goto For_Begin;
									}
								}
								break;
							}
							case 2:{
								State *state_J = new State(this, s->Ist.Exit.dst->Ico.U64);
								branch.emplace_back(state_J);
								state_J->add_assert(guard.translate(*state_J), True);
								if (traceState)
									std::cout << "\n+++++++++++++++ push : " << std::hex << state_J->guest_start << " +++++++++++++++\n" << std::endl;

								Variable _next(tIRExpr(irsb->next));
								if (_next.real()) {
									State *state = new State(this, _next);
									branch.emplace_back(state);
									state->add_assert(guard.translate(*state), False);
									if (traceState)
										std::cout << "\n+++++++++++++++ push : " << std::hex << state->guest_start << " +++++++++++++++\n" << std::endl;

								}
								else {
									std::vector<Z3_ast> next_result;
									eval_all(next_result, solv, _next);
									for (auto && re : next_result) {
										uint64_t rgurd;
										Z3_get_numeral_uint64(m_ctx, re, &rgurd);

										State *state = new State(this, rgurd);
										branch.emplace_back(state);
										state->add_assert(guard.translate(*state), False);
										state->add_assert_eq(Variable(m_ctx, Z3_translate(m_ctx, re, *state)), Variable(m_ctx, Z3_translate(m_ctx, _next, *state)));
										if (traceState)
											std::cout << "\n+++++++++++++++ push : " << std::hex << state->guest_start << " +++++++++++++++\n" << std::endl;
										Z3_dec_ref(m_ctx, re);
									}
								}
								Z3_dec_ref(m_ctx, guard_result[0]);
								Z3_dec_ref(m_ctx, guard_result[1]);
								status = Fork;
								goto EXIT;
							}
							}
						}
					}
					case Ist_NoOp: break;
					case Ist_IMark: guest_start = s->Ist.IMark.addr; break;
					case Ist_AbiHint:break; //====== AbiHint(t4, 128, 0x400936:I64) ====== call 0xxxxxxx
					case Ist_PutI: {
						//PutI(840:8xI8)[t10,-1]
						//840:arr->base
						//8x :arr->nElems
						//I8 :arr->elemTy
						//t10:ix
						//-1 :e->Iex.GetI.bias
						auto ix = tIRExpr(s->Ist.PutI.details->ix);
						if (ix.real()) {
							regs.Ist_Put(
								s->Ist.PutI.details->descr->base + (((UInt)((s->Ist.PutI.details->bias + (int)(ix)))) % s->Ist.PutI.details->descr->nElems)*ty2length(s->Ist.PutI.details->descr->elemTy),
								tIRExpr(s->Ist.PutI.details->data)
								);
						}
						else {
							vassert(0);
						}
						break;
					}
					case Ist_Dirty: {
						IRDirty *dirty = s->Ist.Dirty.details;
						auto k = CCall(dirty->cee, dirty->args, Ity_I8);
						switch (guest) {
						case VexArchAMD64:
							regs.Ist_Put(16, Variable(((VexGuestAMD64State*)VexGuestARCHState)->guest_RAX, m_ctx));
							regs.Ist_Put(40, Variable(((VexGuestAMD64State*)VexGuestARCHState)->guest_RBX, m_ctx));
							regs.Ist_Put(24, Variable(((VexGuestAMD64State*)VexGuestARCHState)->guest_RCX, m_ctx));
							regs.Ist_Put(32, Variable(((VexGuestAMD64State*)VexGuestARCHState)->guest_RDX, m_ctx));
							break;
						default:
							vpanic("not support");
						}
						if (dirty->tmp != -1) {
							ir_temp[t_index][dirty->tmp] = k;
						}
						break;
					}

					case Ist_MBE   /*内存总线事件，fence/请求/释放总线锁*/:break;
					case Ist_StoreG:
					case Ist_LoadG:
					case Ist_LLSC:
					default:
						vex_printf("what ppIRStmt %d\n", s->tag);
						vpanic("what ppIRStmt");
					}
					if (NEED_CHECK)
						if (s->tag != Ist_WrTmp) { vex_printf("\n"); }
				}

				switch (irsb->jumpkind) {
				case Ijk_Boring:		break;
				case Ijk_Call:			break;
				case Ijk_Ret:           break;
				case Ijk_SigTRAP:		{
bkp_pass:
					auto _where = CallBackDict.lower_bound(guest_start);
					if (_where != CallBackDict.end()) {
						if (hook_bkp) {
							guest_start = hook_bkp;
							hook_bkp = NULL;
							goto For_Begin;
						}
						else {
							__m256i m32 = mem.Iex_Load(Variable(guest_start, m_ctx), Ity_V256);
							m32.m256i_i8[0] = _where->second.original;
							if (!is_first_bkp_pass) {
								status = (_where->second.cb)(this);//delta maybe changed by callback
								if (status != Running) {
									goto EXIT;
								}
							}
							else {
								is_first_bkp_pass = False;
							}
							if (delta) {
								guest_start = guest_start + delta;
								delta = 0;
								goto For_Begin;
							}
							else {
								pap.start_swap = 2;
								vta.guest_bytes = (UChar *)(&m32);
								vta.guest_bytes_addr = (Addr64)(guest_start);
								vta.traceflags = NULL;
								//vta.traceflags = VEX_TRACE_FE;
								vta.pap = &pap;
								irsb = LibVEX_FrontEnd(&vta, &res, &pxControl);
								int _n = 1;
								for (; (irsb->stmts_used > _n)&&(irsb->stmts[_n]->tag != Ist_WrTmp); _n++) {
								}
								irsb->stmts_used = _n;
								hook_bkp = guest_start + irsb->stmts[0]->Ist.IMark.len;
								irsb->jumpkind = Ijk_SigTRAP;
								goto For_Begin_NO_Trans;
							}
						}
					}
				}
				case Ijk_Sys_syscall: 
				case Ijk_NoDecode:	
				case Ijk_ClientReq:    
				case Ijk_Yield:        
				case Ijk_EmWarn:       
				case Ijk_EmFail:       
				case Ijk_MapFail:      
				case Ijk_InvalICache:  
				case Ijk_FlushDCache:  
				case Ijk_NoRedir:      
				case Ijk_SigILL:       
				case Ijk_SigSEGV:      
				case Ijk_SigBUS:       
				case Ijk_SigFPE:       
				case Ijk_SigFPE_IntDiv:
				case Ijk_SigFPE_IntOvf:
				case Ijk_Sys_int32:    
				case Ijk_Sys_int128:   
				case Ijk_Sys_int129:   
				case Ijk_Sys_int130:   
				case Ijk_Sys_int145:   
				case Ijk_Sys_int210:   
				case Ijk_Sys_sysenter:
				default:
					status = Ijk_call_back(this, irsb->jumpkind);
					if (status != Running) {
						goto EXIT;
					}
					if (delta) {
						guest_start = guest_start + delta;
						delta = 0;
						goto For_Begin;
					}
				}



				Variable next = tIRExpr(irsb->next);
				if (next.real()) {
					guest_start = next;
				}
				else {
					std::vector<Z3_ast> result;
					
					switch (eval_all(result, solv, next)) {
					case 0: next.~Variable(); goto EXIT;
					case 1:
						Z3_get_numeral_uint64(m_ctx, result[0], &guest_start);
						Z3_dec_ref(m_ctx, result[0]);
						break;
					default:
						for (auto && re : result) {
							uint64_t rgurd;
							Z3_get_numeral_uint64(m_ctx, re, &rgurd);

							State *state = new State(this, rgurd);
							branch.emplace_back(state);

							state->add_assert_eq(Variable(m_ctx, Z3_translate(m_ctx, re, *state)), next.translate(*state));
							if (traceState)
								std::cout << "\n+++++++++++++++ push : " << std::hex << state->guest_start << " +++++++++++++++\n" << std::endl;
							Z3_dec_ref(m_ctx, re);
						}
						status = Fork;
						next.~Variable();
						goto EXIT;
					}
				}
			};

		}
		catch (...) {
			std::cout << "W MEM ERR at " << std::hex << guest_start << std::endl;
			status = Death;
		}
	}
	catch (exception &error) {
		vex_printf("unexpected z3 error: at %llx\n", guest_start);
		std::cout << error << std::endl;
		status = Death;
	}
	
EXIT:
	thread_unregister();
	for (auto son : branch) {
		pool->enqueue([son] {
			son->start(False);
		});
	}
}



#include "Compress.hpp"


#include "../SimulationEngine/Unop.hpp"
#include "../SimulationEngine/Binop.hpp"
#include "../SimulationEngine/Triop.hpp"
#include "../SimulationEngine/Qop.hpp"
#include "State_class_CD.hpp"

