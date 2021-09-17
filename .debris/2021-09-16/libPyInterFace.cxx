
#define Py_LIMITED_API
#ifdef _DEBUG
#undef _DEBUG
#include <python\Python.h>
#define _DEBUG 1
#else
#include <python\Python.h>
#endif

#include "engine/state_class.h"
#include "engine/guest_layout_helper.h"

//
//class PyInterFace : private State {
//public:
//    PyObject* base;
//
//    //call back
//    static PyObject* (*pState_fork)(PyObject*);
//    static State_Tag (*pState_Ijk_cb)(State*, IRJumpKind);
//
//    PyInterFace(const char* filename, Addr64 gse, Bool _need_record, PyObject* _base,
//        State_Tag(*_pState_Ijk_cb)(State*, IRJumpKind),
//        PyObject* (*_pState_fork)(PyObject*)
//    ) :
//        State(filename, gse, _need_record),
//        base(_base)
//    {
//        if (base) Py_IncRef(base);
//        pState_Ijk_cb = _pState_Ijk_cb;
//        pState_fork = _pState_fork;
//    };
//
//    PyInterFace(PyInterFace* father_state, Addr64 gse, PyObject* _base = NULL) :
//        State(father_state, gse),
//        base(_base)
//    {
//        if (base) Py_IncRef(base);
//        else {
//            assert(father_state->base);
//            base = pState_fork(father_state->base);
//            assert(base);
//            if (base) Py_IncRef(base);
//        }
//    }
//   
//
//    State_Tag Ijk_call(IRJumpKind k) {
//        return pState_Ijk_cb(this, k);
//    };
//
//    State* newForkState(ADDR ges) {
//        return new PyInterFace(this, ges);
//    };
//
//    ~PyInterFace() {
//        if (base) Py_DecRef(base);
//    }
//
//};
//
//
//PyObject* (*PyInterFace::pState_fork)(PyObject*);
//State_Tag (*PyInterFace::pState_Ijk_cb)(State*, IRJumpKind);
//
//
//
//
//
//
//
//
//
//
//
//extern "C" {
//    //#include "TR_API_EXP.in"
//}
//
//
//
//#define pyAndC_Def(type)                                                        \
//template<class T,class toTy>                                                    \
//inline PyObject* cvector2list_##type(T cvector)                                 \
//{                                                                               \
//    PyObject* result = PyList_New(0);                                           \
//    for (auto value : cvector) {                                                \
//        PyList_Append(result, PyLong_From##type((toTy)(value)));                \
//    }                                                                           \
//    Py_IncRef(result);\
//    return result;                                                              \
//}                                                                               \
//                                                                                \
//template<class T, class Ty>                                                     \
//inline void list2cvector_##type(T vector, PyObject* obj)                        \
//{                                                                               \
//    if (PyList_Check(obj)) {                                                    \
//        for (Py_ssize_t i = 0; i < PyList_Size(obj); i++) {                     \
//            PyObject *value = PyList_GetItem(obj, i);                           \
//            vector.emplace_back((Ty)PyLong_As##type(value));                    \
//        }                                                                       \
//    }                                                                           \
//}
//
//
//pyAndC_Def(LongLong)
//pyAndC_Def(Long)
//
//
////State *     TB_top_state(
////    PyObject *base ,
////    Super superState_cb, 
////    State_Tag(*func_cb)(State *, IRJumpKind),
////    char *filename,
////    Addr64 oep,
////    Bool need_record
////) {
////    pState_fork = superState_cb;
////    Ijk_call_back = func_cb;
////    return new State(filename, oep, need_record, base);
////}
//
//HMODULE     TB_Z3_Model_Handle() { return  GetModuleHandle(TEXT("libz3.dll")); }
////State *     TB_state_fork(PyObject *base, State * father, Addr64 oep) { return new State(father, oep, base); }
////PyObject *  TB_cState2pState(State * s) {  
////    Py_IncRef(s->base);
////    return s->base;
////}
//
//Addr64      TB_state_guest_start(State* s) { return s->get_cpu_ip(); }
//Addr64      TB_state_guest_start_ep(State* s) { return s->get_state_ep(); }
//State_Tag   TB_state_status(State* s) { return s->status; }
////void        TB_state_start(State * s) {
////    pool->enqueue([s] {
////        s->start(True);
////    });
////}
////void        TB_thread_wait() { pool->wait(); }
//void        TB_state_delta(State* s, Long length) { s->hook_pass(length); }
//void        TB_state_compress(State* s, Addr64 Target_Addr, State_Tag tag, PyObject* avoid) {
//    std::vector<State_Tag> ds;
//    list2cvector_Long<std::vector<State_Tag>, State_Tag>(ds, avoid);
//    s->compress(Target_Addr, tag, ds);
//}
//PyObject* TB_state_branch(State* s) { return cvector2list_LongLong<std::vector<State*>, ULong>(s->branch); }
//void        TB_hook_add(State* s, Addr64 addr, TRtype::Hook_CB func) {
//    s->hook_add(addr, func);
//}
////void        TB_idx2tableValueDecl_add(Addr64 addr, TRtype::TableIdx_CB func) { TableIdxDict[addr] = func; };
//ULong       TB_mem_map(State* s, Addr64 address, ULong length) { return s->mem.map(address, length); }
//ULong       TB_mem_unmap(State* s, Addr64 address, ULong length) { return s->mem.unmap(address, length); }
//Z3_solver   TB_state_solver(State* s) { return s->solv; }
//Z3_context  TB_state_ctx(State* s) { return *s; };
//void        TB_state_add_assert(State* s, Z3_ast assert, Bool ToF) { s->add_assert(Vns(s->m_ctx, assert, 1), ToF); }
//
//void regs_r_write1(State* s, UShort offset, UChar     value) { s->regs.Ist_Put(offset, value); }
//void regs_r_write2(State* s, UShort offset, UShort    value) { s->regs.Ist_Put(offset, value); }
//void regs_r_write4(State* s, UShort offset, UInt      value) { s->regs.Ist_Put(offset, value); }
//void regs_r_write8(State* s, UShort offset, ULong     value) { s->regs.Ist_Put(offset, value); }
//
//void regs_s_write(State* s, UShort offset, Z3_ast    value) { s->regs.Ist_Put(offset, Vns(s->m_ctx, value)); }
//void regs_s_write1(State* s, UShort offset, Z3_ast    value) { s->regs.Ist_Put<8>(offset, value); }
//void regs_s_write2(State* s, UShort offset, Z3_ast    value) { s->regs.Ist_Put<16>(offset, value); }
//void regs_s_write4(State* s, UShort offset, Z3_ast    value) { s->regs.Ist_Put<32>(offset, value); }
//void regs_s_write8(State* s, UShort offset, Z3_ast    value) { s->regs.Ist_Put<64>(offset, value); }
//
//#define regs_read_def(nbytes,nbit,T)                                    \
//Z3_ast regs_read##nbytes##(State *s, T *result, UShort offset) {        \
//    Vns v = s->regs.Iex_Get(offset, Ity_I##nbit##);                     \
//    if (v.real()) {                                                     \
//        *result = v;                                                    \
//        return NULL;                                                    \
//    }                                                                   \
//    else {                                                              \
//        Z3_inc_ref(*s,v);                                               \
//        return v;                                                       \
//    }                                                                   \
//}                                                                       \
//
//regs_read_def(1, 8, UChar)
//regs_read_def(2, 16, UShort)
//regs_read_def(4, 32, UInt)
//regs_read_def(8, 64, ULong)
//
//
//void mem_r_r_write1(State* s, Addr64 offset, UChar  value) { s->mem.Ist_Store(offset, value); }
//void mem_r_r_write2(State* s, Addr64 offset, UShort value) { s->mem.Ist_Store(offset, value); }
//void mem_r_r_write4(State* s, Addr64 offset, UInt   value) { s->mem.Ist_Store(offset, value); }
//void mem_r_r_write8(State* s, Addr64 offset, ULong  value) { s->mem.Ist_Store(offset, value); }
//
//void mem_r_s_write1(State* s, Addr64 offset, Z3_ast value) { s->mem.Ist_Store<8>(offset, value); }
//void mem_r_s_write2(State* s, Addr64 offset, Z3_ast value) { s->mem.Ist_Store<16>(offset, value); }
//void mem_r_s_write4(State* s, Addr64 offset, Z3_ast value) { s->mem.Ist_Store<32>(offset, value); }
//void mem_r_s_write8(State* s, Addr64 offset, Z3_ast value) { s->mem.Ist_Store<64>(offset, value); }
//
//void mem_s_r_write1(State* s, Z3_ast offset, UChar  value) { s->mem.Ist_Store(offset, value); }
//void mem_s_r_write2(State* s, Z3_ast offset, UShort value) { s->mem.Ist_Store(offset, value); }
//void mem_s_r_write4(State* s, Z3_ast offset, UInt   value) { s->mem.Ist_Store(offset, value); }
//void mem_s_r_write8(State* s, Z3_ast offset, ULong  value) { s->mem.Ist_Store(offset, value); }
//
//void mem_s_s_write1(State* s, Z3_ast offset, Z3_ast value) { s->mem.Ist_Store<8>(offset, value); }
//void mem_s_s_write2(State* s, Z3_ast offset, Z3_ast value) { s->mem.Ist_Store<16>(offset, value); }
//void mem_s_s_write4(State* s, Z3_ast offset, Z3_ast value) { s->mem.Ist_Store<32>(offset, value); }
//void mem_s_s_write8(State* s, Z3_ast offset, Z3_ast value) { s->mem.Ist_Store<64>(offset, value); }
//
//
//
//#define mem_read_e_def(nbytes,nbit,T)                                       \
//Z3_ast mem_r_read##nbytes##(State *s, T *result, Addr64 addr) {             \
//    Vns v = s->mem.Iex_Load<Ity_I##nbit>(addr);                             \
//    if (v.real()) {                                                         \
//        *result = v;                                                        \
//        return NULL;                                                        \
//    }                                                                       \
//    else {                                                                  \
//        Z3_inc_ref(s->m_ctx,v);                                             \
//        return v;                                                           \
//    }                                                                       \
//}
//
//#define mem_read_s_def(nbytes,nbit,T)                                       \
//Z3_ast mem_s_read##nbytes##(State *s, T *result, Z3_ast addr) {             \
//    vex_printf("st\n");\
//    Vns v = s->mem.Iex_Load<Ity_I##nbit>(addr);                             \
//    vex_printf("et\n");\
//    if (v.real()) {                                                         \
//        *result = v;                                                        \
//        return NULL;                                                        \
//    }                                                                       \
//    else {                                                                  \
//        Z3_inc_ref(s->m_ctx,v);                                             \
//        return v;                                                           \
//    }                                                                       \
//}                                                                           \
//
//
//
//mem_read_e_def(1, 8, UChar)
//mem_read_e_def(2, 16, UShort)
//mem_read_e_def(4, 32, UInt)
//mem_read_e_def(8, 64, ULong)
//
//mem_read_s_def(1, 8, UChar)
//mem_read_s_def(2, 16, UShort)
//mem_read_s_def(4, 32, UInt)
//mem_read_s_def(8, 64, ULong)
//
//
//
//
//
//
//
//
//
//
//
//
