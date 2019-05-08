// TriggerBug.cpp: 定义应用程序的入口点。
//	 23333


//#define NEED_CHECK	
//#define OPSTR
#define PUSHPOPTRACE
#define HOSTARCH VexArchAMD64

//#undef _DEBUG
//#define z3ss
#define DLL_EXPORTS
#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\TriggerBug-asong.xml"

#include "engine.hpp"
#include "../../tinyxml2/tinyxml2.h"
#include "libvex_init.hpp"
#include "Thread_Pool/ThreadPool.hpp"
#include "SimulationEngine/Variable.hpp"
#include "SimulationEngine/Register.hpp"
#include "SimulationEngine/memory.hpp"
#include "StateClass/State_class.hpp"

ThreadPool *pool = NULL;
std::hash_map<Addr64, Hook_struct> CallBackDict;
State_Tag (*Ijk_call_back)(State *, IRJumpKind );
tinyxml2::XMLDocument doc;
VexArch guest;



#define pyAndC_Def(type)															\
template<class T,class toTy>														\
inline PyObject* cvector2list_##type(T cvector)										\
{																					\
	PyObject* result = PyList_New(0);												\
	for (auto value : cvector) {													\
		PyList_Append(result, PyLong_From##type((toTy)(value)));					\
	}																				\
	return result;																	\
}																					\
																					\
template<class T, class Ty>															\
inline void list2cvector_##type(T vector, PyObject* obj)							\
{																					\
	if (PyList_Check(obj)) {														\
		for (Py_ssize_t i = 0; i < PyList_Size(obj); i++) {						\
			PyObject *value = PyList_GetItem(obj, i);								\
			vector.emplace_back((Ty)PyLong_As##type(value));						\
		}																			\
	}																				\
}


pyAndC_Def(LongLong)
pyAndC_Def(Long)

extern "C"
{
	DLLDEMO_API State *  new_state(char *filename, Addr64 oep, Bool need_record);
	DLLDEMO_API State *  new_state_fork(State * father, Addr64 oep);
	DLLDEMO_API void state_go(State *);
	DLLDEMO_API void state_compress(State * s, Addr64 Target_Addr, State_Tag tag, PyObject* avoid);
	DLLDEMO_API void state_add_assert(State *s, Z3_ast assert, Bool ToF);
	DLLDEMO_API Z3_context StateCtx(State *);
	DLLDEMO_API void hook_add(State *, Addr64 , CallBack );
	DLLDEMO_API Addr64 state_guest_start(State *); 
	DLLDEMO_API Addr64 state_guest_start_ep(State *); 
	DLLDEMO_API State_Tag state_status(State *);
	DLLDEMO_API Z3_solver state_solver(State *);
	DLLDEMO_API HMODULE Z3_Model_Handle();
	DLLDEMO_API PyObject* stateBranch(State *s);
	DLLDEMO_API void init_Ijk_call_back(State_Tag(*func)(State *, IRJumpKind));
	DLLDEMO_API void hook_pass_code(State *s, Long length);
	
	DLLDEMO_API void regs_r_write1(State *s, UShort offset, UChar  value);
	DLLDEMO_API void regs_r_write2(State *s, UShort offset, UShort value);
	DLLDEMO_API void regs_r_write4(State *s, UShort offset, UInt   value);
	DLLDEMO_API void regs_r_write8(State *s, UShort offset, ULong  value);

	DLLDEMO_API void regs_s_write(State *s, UShort offset, Z3_ast value);

	DLLDEMO_API void regs_s_write1(State *s, UShort offset, Z3_ast value);
	DLLDEMO_API void regs_s_write2(State *s, UShort offset, Z3_ast value);
	DLLDEMO_API void regs_s_write4(State *s, UShort offset, Z3_ast value);
	DLLDEMO_API void regs_s_write8(State *s, UShort offset, Z3_ast value);

	DLLDEMO_API Z3_ast regs_read1(State *s, UChar  *result, UShort offset);
	DLLDEMO_API Z3_ast regs_read2(State *s, UShort *result, UShort offset);
	DLLDEMO_API Z3_ast regs_read4(State *s, UInt   *result, UShort offset);
	DLLDEMO_API Z3_ast regs_read8(State *s, ULong  *result, UShort offset);

	DLLDEMO_API void mem_r_r_write1(State *s, Addr64 offset, UChar  value);
	DLLDEMO_API void mem_r_r_write2(State *s, Addr64 offset, UShort value);
	DLLDEMO_API void mem_r_r_write4(State *s, Addr64 offset, UInt   value);
	DLLDEMO_API void mem_r_r_write8(State *s, Addr64 offset, ULong  value);
																		  
	DLLDEMO_API void mem_r_s_write1(State *s, Addr64 offset, Z3_ast value);
	DLLDEMO_API void mem_r_s_write2(State *s, Addr64 offset, Z3_ast value);
	DLLDEMO_API void mem_r_s_write4(State *s, Addr64 offset, Z3_ast value);
	DLLDEMO_API void mem_r_s_write8(State *s, Addr64 offset, Z3_ast value);
																		  
	DLLDEMO_API void mem_s_r_write1(State *s, Z3_ast offset, UChar  value);
	DLLDEMO_API void mem_s_r_write2(State *s, Z3_ast offset, UShort value);
	DLLDEMO_API void mem_s_r_write4(State *s, Z3_ast offset, UInt   value);
	DLLDEMO_API void mem_s_r_write8(State *s, Z3_ast offset, ULong  value);
																		  
	DLLDEMO_API void mem_s_s_write1(State *s, Z3_ast offset, Z3_ast value);
	DLLDEMO_API void mem_s_s_write2(State *s, Z3_ast offset, Z3_ast value);
	DLLDEMO_API void mem_s_s_write4(State *s, Z3_ast offset, Z3_ast value);
	DLLDEMO_API void mem_s_s_write8(State *s, Z3_ast offset, Z3_ast value);

	DLLDEMO_API Z3_ast mem_r_read1(State *s, UChar  *result, Addr64 addr);
	DLLDEMO_API Z3_ast mem_r_read2(State *s, UShort *result, Addr64 addr);
	DLLDEMO_API Z3_ast mem_r_read4(State *s, UInt   *result, Addr64 addr);
	DLLDEMO_API Z3_ast mem_r_read8(State *s, ULong  *result, Addr64 addr);


	DLLDEMO_API Z3_ast mem_s_read1(State *s, UChar  *result, Z3_ast addr);
	DLLDEMO_API Z3_ast mem_s_read2(State *s, UShort *result, Z3_ast addr);
	DLLDEMO_API Z3_ast mem_s_read4(State *s, UInt   *result, Z3_ast addr);
	DLLDEMO_API Z3_ast mem_s_read8(State *s, ULong  *result, Z3_ast addr);

	DLLDEMO_API ULong mem_map(State *s, Addr64 address, ULong length);
	DLLDEMO_API ULong mem_unmap(State *s, Addr64 address, ULong length);
}

ULong mem_map(State *s, Addr64 address, ULong length) { return s->mem.map(address, length); }
ULong mem_unmap(State *s, Addr64 address, ULong length) { return s->mem.unmap(address, length); }

Variable ir_temp[MAX_THREADS][400];

LARGE_INTEGER   freq_global = { 0 };
LARGE_INTEGER   beginPerformanceCount_global = { 0 };
LARGE_INTEGER   closePerformanceCount_global = { 0 };

void init_Ijk_call_back(State_Tag(*func)(State *, IRJumpKind) ) { Ijk_call_back = func; }

State * new_state(char *filename, Addr64 oep, Bool need_record) { return new State(filename, oep, need_record); }
State * new_state_fork(State * father, Addr64 oep) { return new State(father, oep); }
Addr64 state_guest_start(State *s) { return s->get_guest_start(); }
Addr64 state_guest_start_ep(State *s) { return s->get_guest_start_ep(); }
State_Tag state_status(State *s) { return s->status; }
Z3_solver state_solver(State *s) { return s->solv; }
void state_add_assert(State *s, Z3_ast assert, Bool ToF) { s->add_assert(Variable(s->m_ctx,assert,1), ToF); }
HMODULE Z3_Model_Handle() { return  GetModuleHandle(TEXT("libz3.dll")); }
void state_go(State * s) {
	pool->enqueue([s] {
		s->start(True);
	});
	pool->wait();
}
void state_compress(State * s, Addr64 Target_Addr, State_Tag tag, PyObject* avoid) {
	std::vector<State_Tag> ds;
	list2cvector_Long<std::vector<State_Tag>,State_Tag>(ds, avoid);
	s->compress(Target_Addr, tag, ds);
}
PyObject* stateBranch(State *s) { return cvector2list_LongLong<std::vector<State*>,ULong>(s->branch); }
Z3_context StateCtx(State *s) { return *s; };
void hook_pass_code(State *s, Long length) { s->delta = length; }









void regs_r_write1(State *s, UShort offset, UChar     value) { s->regs.Ist_Put<e_real>(offset, Variable(value, s->m_ctx)); }
void regs_r_write2(State *s, UShort offset, UShort    value) { s->regs.Ist_Put<e_real>(offset, Variable(value, s->m_ctx)); }
void regs_r_write4(State *s, UShort offset, UInt      value) { s->regs.Ist_Put<e_real>(offset, Variable(value, s->m_ctx)); }
void regs_r_write8(State *s, UShort offset, ULong     value) { s->regs.Ist_Put<e_real>(offset, Variable(value, s->m_ctx)); }

void regs_s_write(State *s, UShort offset, Z3_ast    value) { s->regs.Ist_Put<e_symbolic>(offset, Variable(s->m_ctx, value)); }
void regs_s_write1(State *s, UShort offset, Z3_ast    value) { s->regs.Ist_Put<e_symbolic>(offset, Variable(s->m_ctx, value,8  )); }
void regs_s_write2(State *s, UShort offset, Z3_ast    value) { s->regs.Ist_Put<e_symbolic>(offset, Variable(s->m_ctx, value,16 )); }
void regs_s_write4(State *s, UShort offset, Z3_ast    value) { s->regs.Ist_Put<e_symbolic>(offset, Variable(s->m_ctx, value,32 )); }
void regs_s_write8(State *s, UShort offset, Z3_ast    value) { s->regs.Ist_Put<e_symbolic>(offset, Variable(s->m_ctx, value,64 )); }



#define regs_read_def(nbytes,nbit,T)									\
Z3_ast regs_read##nbytes##(State *s, T *result, UShort offset) {		\
	Variable v = s->regs.Iex_Get(offset, Ity_I##nbit##);				\
	if (v.real()) {												\
		*result = v;													\
		return NULL;													\
	}																	\
	else {																\
		Z3_inc_ref(v,v);												\
		return v;														\
	}																	\
}																		\

regs_read_def(1,  8, UChar)
regs_read_def(2, 16, UShort)
regs_read_def(4, 32, UInt)
regs_read_def(8, 64, ULong)




void mem_r_r_write1(State *s, Addr64 offset, UChar  value) { s->mem.Ist_Store<e_real, e_real>(Variable(offset, s->m_ctx), Variable(value, s->m_ctx)); }
void mem_r_r_write2(State *s, Addr64 offset, UShort value) { s->mem.Ist_Store<e_real, e_real>(Variable(offset, s->m_ctx), Variable(value, s->m_ctx)); }
void mem_r_r_write4(State *s, Addr64 offset, UInt   value) { s->mem.Ist_Store<e_real, e_real>(Variable(offset, s->m_ctx), Variable(value, s->m_ctx)); }
void mem_r_r_write8(State *s, Addr64 offset, ULong  value) { s->mem.Ist_Store<e_real, e_real>(Variable(offset, s->m_ctx), Variable(value, s->m_ctx)); }

void mem_r_s_write1(State *s, Addr64 offset, Z3_ast value) { s->mem.Ist_Store<e_real, e_symbolic>(Variable(offset, s->m_ctx), Variable(s->m_ctx, value)); }
void mem_r_s_write2(State *s, Addr64 offset, Z3_ast value) { s->mem.Ist_Store<e_real, e_symbolic>(Variable(offset, s->m_ctx), Variable(s->m_ctx, value)); }
void mem_r_s_write4(State *s, Addr64 offset, Z3_ast value) { s->mem.Ist_Store<e_real, e_symbolic>(Variable(offset, s->m_ctx), Variable(s->m_ctx, value)); }
void mem_r_s_write8(State *s, Addr64 offset, Z3_ast value) { s->mem.Ist_Store<e_real, e_symbolic>(Variable(offset, s->m_ctx), Variable(s->m_ctx, value)); }

void mem_s_r_write1(State *s, Z3_ast offset, UChar  value) { s->mem.Ist_Store<e_symbolic, e_real>(Variable(offset, s->m_ctx), Variable(value, s->m_ctx)); }
void mem_s_r_write2(State *s, Z3_ast offset, UShort value) { s->mem.Ist_Store<e_symbolic, e_real>(Variable(offset, s->m_ctx), Variable(value, s->m_ctx)); }
void mem_s_r_write4(State *s, Z3_ast offset, UInt   value) { s->mem.Ist_Store<e_symbolic, e_real>(Variable(offset, s->m_ctx), Variable(value, s->m_ctx)); }
void mem_s_r_write8(State *s, Z3_ast offset, ULong  value) { s->mem.Ist_Store<e_symbolic, e_real>(Variable(offset, s->m_ctx), Variable(value, s->m_ctx)); }

void mem_s_s_write1(State *s, Z3_ast offset, Z3_ast value) { s->mem.Ist_Store<e_symbolic, e_symbolic>(Variable(offset, s->m_ctx), Variable(s->m_ctx, value)); }
void mem_s_s_write2(State *s, Z3_ast offset, Z3_ast value) { s->mem.Ist_Store<e_symbolic, e_symbolic>(Variable(offset, s->m_ctx), Variable(s->m_ctx, value)); }
void mem_s_s_write4(State *s, Z3_ast offset, Z3_ast value) { s->mem.Ist_Store<e_symbolic, e_symbolic>(Variable(offset, s->m_ctx), Variable(s->m_ctx, value)); }
void mem_s_s_write8(State *s, Z3_ast offset, Z3_ast value) { s->mem.Ist_Store<e_symbolic, e_symbolic>(Variable(offset, s->m_ctx), Variable(s->m_ctx, value)); }



#define mem_read_e_def(nbytes,nbit,T)											\
Z3_ast mem_r_read##nbytes##(State *s, T *result, Addr64 addr) {			\
	Variable v = s->mem.Iex_Load(Variable(addr,s->m_ctx), Ity_I##nbit##);\
	if (v.real()) {												\
		*result = v;													\
		return NULL;													\
	}																	\
	else {																\
		Z3_inc_ref(v,v);												\
		return v;														\
	}																	\
}																		\

#define mem_read_s_def(nbytes,nbit,T)									\
Z3_ast mem_s_read##nbytes##(State *s, T *result, Z3_ast addr) {		\
	Variable v = s->mem.Iex_Load(Variable(s->m_ctx, addr), Ity_I##nbit##);\
	if (v.real()) {												\
		*result = v;													\
		return NULL;													\
	}																	\
	else {																\
		Z3_inc_ref(v,v);												\
		return v;														\
	}																	\
}																		\



mem_read_e_def(1,  8, UChar)
mem_read_e_def(2, 16, UShort)
mem_read_e_def(4, 32, UInt)
mem_read_e_def(8, 64, ULong)

mem_read_s_def(1,  8, UChar)
mem_read_s_def(2, 16, UShort)
mem_read_s_def(4, 32, UInt)
mem_read_s_def(8, 64, ULong)



void hook_add(State *s, Addr64 addr, CallBack func) {
	if (CallBackDict.find(addr) == CallBackDict.end()) {
		auto P = s->getMemPage(addr);
		CallBackDict[addr] = Hook_struct{ func ,P->unit->m_bytes[addr & 0xfff] };
		P->unit->m_bytes[addr & 0xfff] = 0xCC;
	}
	else {
		CallBackDict[addr].cb = func;
	}
}







//
//
//int nasj(State *s) {
//	char buff[20];
//	auto rax = s->regs.Iex_Get(16, Ity_I64);
//	auto rsi = s->regs.Iex_Get(64, Ity_I64);
//	ULong max = 38;
//	if ((ULong)rax == 0) {
//		for (int ncouu = 0; ncouu < max; ncouu++) {
//			sprintf_s(buff, sizeof(buff), "flag%d", ncouu);
//			auto sym = s->m_ctx.bv_const(buff, 8);
//			s->mem.Ist_Store<e_real, e_symbolic>(Variable((ULong)rsi + ncouu, *s, 64), Variable(*s, sym, 8));
//			s->add_assert(sym < 125, True);
//			s->add_assert(sym > 30, True);
//			s->add_assert(sym != 32, True);
//		}
//		s->mem.Ist_Store<e_real, e_real>(Variable((ULong)rsi + max, *s, 64), Variable((UShort)0x000A,*s, 8));
//		s->regs.Ist_Put(16, Variable(max+1, *s, 64));
//
//		s->solv.push();
//
//		if (s->solv.check() == sat) {
//			vex_printf("sat");
//			auto m = s->solv.get_model();
//			std::cout << m << std::endl;
//			std::cout << s->solv.assertions() << std::endl;
//		}
//		else {
//			vex_printf("unsat??????????\n\n");
//		}
//
//		s->solv.pop();
//
//
//		return Running;
//	}
//	else if ((ULong)rax == 5) {
//		return Running;
//	}
//	else {
//		return Death;
//	}
//	
//}
//int eee(State *s) {
//	s->solv.push();
//	
//	if (s->solv.check() == sat) {
//		vex_printf("sat");
//		auto m = s->solv.get_model();
//		std::cout << m << std::endl;
//	}
//	else {
//		vex_printf("unsat??????????\n\n");
//	}
//
//	s->solv.pop();
//	return 300;
//}
int comp1(State *s) {
	return Running;
}




int main() {
	//call_back_syscall = (CallBack)nasj;


	State s(INIFILENAME, NULL, True);
	
	context test;




	auto kkkk = test.bv_val(-10, 64);
	auto gggg = test.bv_val(  6, 64);


	
	auto P = s.mem.getMemPage(0x00007FFFF7FE9268);
	SET1((P->unit->m_bytes + (0x00007FFFF7FE9268+1 & 0xfff)), 0xAE);

	auto sd = &s;
	s.regs.Ist_Put(176, Variable(00ull, s, 64));
	auto f = (Variable)s.m_ctx.bv_const("jjj", 64);
	s.add_assert(f <60, 1);
	s.regs.Ist_Put(32, f);
	hook_add(&s, 0x7FFFF7E34CD6, (CallBack)comp1);
	/*hook_add(&s, 0x0004081DF, (CallBack)eee);
	hook_add(&s, 0x00406A75, (CallBack)comp1);
	*/
	//hook_add(&s, 0x406A75, (CallBack)comp1);
	

	/*auto P = s.mem.getMemPage(0x7ffff7dec7b8);
	SET4((P->unit->m_bytes + (0x7ffff7dec7b8 & 0xfff)), 0x90909090);
	SET1((P->unit->m_bytes + (0x7ffff7dec7b8 & 0xfff + 4)), 0x90);

	SET4((P->unit->m_bytes + (0x7FFFF7DEC7D4 & 0xfff)), 0x90909090);
	SET1((P->unit->m_bytes + (0x7FFFF7DEC7D4 & 0xfff + 4)), 0x90);*/
	pool->enqueue([sd] {
		sd->start(True);
	});
	TESTCODE(
		pool->wait();
	)

	std::cout << *sd << std::endl;

	//while (true)
	//{
	//	
	//	std::cout << *sd << std::endl;
	//	if (sd->status == Death) break;
	//	if (sd->branch.size()) {
	//		std::vector<State_Tag> ds;
	//		ds.emplace_back(Death);
	//		sd->compress(0x00406A75, (State_Tag)0x00406A75, ds);
	//		sd->pass_hook_once = True;
	//	}
	//	else {
	//		sd->pass_hook_once = True;
	//		sd->status = NewState;
	//	}
	//}
	//
	memset
	printf("OVER");
	getchar();
	return 0;
}



