
#include "z3_target_call.h"
#include "AMD64/amd64CCall.h"
#include "X86/x86CCall.h"
#include "z3_target_defs.h"
#include "engine/variable.h"
#define _SILENCE_STDEXT_HASH_DEPRECATION_WARNINGS
#include <hash_map>

Z3_ast bv2bool(Z3_context ctx, Z3_ast ast) {
    Z3_inc_ref(ctx, ast);
    Z3_ast one = Z3_mk_int(ctx, 1, Z3_get_sort(ctx, ast));
    Z3_inc_ref(ctx, one);
    Z3_ast result = Z3_mk_eq(ctx, ast, one);
    Z3_dec_ref(ctx, one);
    Z3_dec_ref(ctx, ast);
    return result;
}

Vns parity_table(Vns const&d) {
    Vns all = d.extract(0, 0);
    for (UChar i = 1; i <= 7; i++) {
        all = all + d.extract(i, i);
    }
    return all.extract(0, 0) == 0;
};

UChar* extern_dealy_call(UChar* fuc) {
#ifdef _MSC_VER
    //idt

//00007FFAF6695BCC FF 25 F6 94 1C 00    jmp         qword ptr [00007FFAF685F0C8h]  

    if (((UShort*)fuc)[0] == 0x25FF) {
        UInt offset = *(UInt*)(&fuc[2]) + 6;
        return ((UChar**)(&fuc[offset]))[0];
    }
#else
    //plt
#error "???? arch "
#endif
    vex_printf("func(%p) not found real func", fuc);
    VPANIC("gg");
    return nullptr;
}




thread_local static UChar* old_fuc = NULL;
thread_local static UChar* old_z3_fuc = NULL;
std::hash_map<UChar*, UChar*> fuc_2_Z3_Func_Map;


static void Func_Map_Add(UChar* ir_fuc, UChar* z3_fuc) {
    fuc_2_Z3_Func_Map[ir_fuc] = z3_fuc; 
    UChar* p = extern_dealy_call(ir_fuc);
    if (p) {
        fuc_2_Z3_Func_Map[p] = z3_fuc;
    }
}



static void dirty_Func_Map_Add(UChar* ir_fuc) {
    fuc_2_Z3_Func_Map[ir_fuc] = DIRTY_CALL_MAGIC;
    UChar* p = extern_dealy_call(ir_fuc);
    if (p) {
        fuc_2_Z3_Func_Map[p] = DIRTY_CALL_MAGIC;
    }
}


#define Func_Map_Add(a,b) Func_Map_Add((UChar*)(a),(UChar*)(b))
#define DIRTY_Func_Map_Add(a) dirty_Func_Map_Add((UChar*)(a))

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
        

    //nullptr: 这个函数不可以直接执行 需要使用dirty call 调用
    DIRTY_Func_Map_Add(x86g_use_seg_selector);
}



void* funcDict(void* irfunc) {
    if (old_fuc != irfunc) {
        auto where = fuc_2_Z3_Func_Map.find((UChar*)irfunc);
        if (where == fuc_2_Z3_Func_Map.end()) {
            return NULL;
        }
        old_fuc = (UChar*)irfunc;
        old_z3_fuc = where->second;
        return where->second;
    }
    return old_z3_fuc;
}