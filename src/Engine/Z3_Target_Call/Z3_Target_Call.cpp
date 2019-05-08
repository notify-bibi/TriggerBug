#include "../engine.hpp"
#include "../SimulationEngine/Variable.hpp"
#include "./AMD64/CCall.hpp"
#include "./Z3_Target_Call.hpp"

static void * old_fuc[MAX_THREADS];
static void * old_z3_fuc[MAX_THREADS];
std::hash_map<void*, void*> fuc_2_Z3_Func_Map;


static void Func_Map_Add(void* ir_fuc, void* z3_fuc) {
	fuc_2_Z3_Func_Map[ir_fuc] = z3_fuc;
}
#define Func_Map_Add(a,b) Func_Map_Add((void*)(a),(void*)(b))
void Func_Map_Init() {
	Func_Map_Add(amd64g_calculate_condition, z3_amd64g_calculate_condition);
	for (int i = 0; i < MAX_THREADS; i++) {
		old_fuc[i] = NULL; old_z3_fuc[i] = NULL;
	}
}



void* funcDict(void* irfunc) {
	auto where = fuc_2_Z3_Func_Map.find(irfunc);
	if (where == fuc_2_Z3_Func_Map.end()) {
		vpanic("error func");
		return NULL;
	}
	else {
		auto idx = temp_index();
		if (old_fuc[idx] != irfunc) {
			old_fuc[idx] = irfunc;
			old_z3_fuc[idx] = where->second;
			return where->second;
		}
		return old_fuc[idx];
	}
}