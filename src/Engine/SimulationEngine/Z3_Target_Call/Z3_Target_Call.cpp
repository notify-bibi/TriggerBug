#include "../../engine.hpp"
#include "../Variable.hpp"
#include "./Z3_Target_Call.hpp"


auto parity_table = [](Vns &d) {
    Vns all = d.extract(0, 0);
    for (UChar i = 1; i <= 7; i++) {
        all = all + d.extract(i, i);
    }
    return all.extract(0, 0) == 0;
};

static inline Z3_ast bv2bool(Z3_context ctx, Z3_ast ast) {
    Z3_inc_ref(ctx, ast);
    Z3_ast one = Z3_mk_int(ctx, 1, Z3_get_sort(ctx, ast));
    Z3_inc_ref(ctx, one);
    Z3_ast result = Z3_mk_eq(ctx, ast, one);
    Z3_dec_ref(ctx, one);
    Z3_dec_ref(ctx, ast);
    return result;
}

#define bit2ret(v, idx)  ((v).real()) ? Vns((Z3_context)(v), ((v)>>(idx)), 1) : Vns((Z3_context)(v), bv2bool((Z3_context)(v), Vns((Z3_context)(v),Z3_mk_extract(v,idx,idx,v),1)),1)


#define NOTEMACRO(...)  
#define MACRO(a) a

#define UChar_extract(value) ((value).extract(7,0))
#define UShort_extract(value) ((value).extract(15,0))
#define UInt_extract(value) ((value).extract(31,0))
#define ULong_extract(value) (value)


#include "./AMD64/CCall.hpp"
#include "./X86/CCall.hpp"

thread_local static void* old_fuc = NULL;
thread_local static void* old_z3_fuc = NULL;
std::hash_map<void*, void*> fuc_2_Z3_Func_Map;


static void Func_Map_Add(void* ir_fuc, void* z3_fuc) {
    fuc_2_Z3_Func_Map[ir_fuc] = z3_fuc;
}
#define Func_Map_Add(a,b) Func_Map_Add((void*)(a),(void*)(b))
void Func_Map_Init() {
//AMD64:
    Func_Map_Add(amd64g_calculate_condition, z3_amd64g_calculate_condition);
    Func_Map_Add(amd64g_calculate_rflags_c, z3_amd64g_calculate_rflags_c);
    Func_Map_Add(amd64g_calculate_rflags_all, z3_amd64g_calculate_rflags_all);
//X86:
    Func_Map_Add(x86g_calculate_eflags_c, z3_x86g_calculate_eflags_c);
    Func_Map_Add(x86g_calculate_condition, z3_x86g_calculate_condition);
    Func_Map_Add(x86g_calculate_eflags_all, z3_x86g_calculate_eflags_all);
    vassert(old_fuc == NULL && old_z3_fuc == NULL);
        
}



void* funcDict(void* irfunc) {
    if (old_fuc != irfunc) {
        auto where = fuc_2_Z3_Func_Map.find(irfunc);
        if (where == fuc_2_Z3_Func_Map.end()) {
            return NULL;
        }
        old_fuc = irfunc;
        old_z3_fuc = where->second;
        return where->second;
    }
    return old_z3_fuc;
}