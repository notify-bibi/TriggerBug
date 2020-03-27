#pragma once
#include "test.h"
#include "engine/basic_var.hpp"


using namespace TR;


//using Vns = sv::tval;



void test1() {
    z3::context c;

    cbool bo1(c, false);
    cbool bo2(c, true);

    std::cout << (bo1 ^ bo2) << std::endl;
    std::cout << (bo1 ||  bo2) << std::endl;
    std::cout << (bo1 && bo2) << std::endl;

    rcval<uint16_t>  uint16(c, 0xffff);
    rcval<int16_t>  int16(c, 0xffff);
    rcval<int32_t>  int32(c, -1);
    rcval<uint32_t>  uint32(c, -1ull);
    sv::ctype_val< true, 48, Z3_BV_SORT> int48(c, 1ll << 47);
    sv::ctype_val< false, 48, Z3_BV_SORT> uint48(c, 1ll << 47);

    rcval<__m128i>  m128(c, _mm_set1_epi8(9));
    rcval<__m256i>  m256(c, _mm256_set_epi64x(9, 6, 3, 1));

    __m128i i128 = m128;


    std::cout << int16 << std::endl;
    std::cout << uint32 << std::endl;
    std::cout << uint32 << std::endl;
    std::cout << int48 << std::endl;
    std::cout <<(int48 >> 8) << std::endl;
    std::cout << (uint48 >> 8) << std::endl;
    std::cout << (int48 > 0) << std::endl;
    std::cout << (uint48 > 0) << std::endl;



    std::cout << (int16 >= 8) << std::endl;
    std::cout << uint32 + 8989 << std::endl;
    std::cout << uint32 - 89 << std::endl;


    std::cout << m128 << std::endl;
    std::cout << m256 << std::endl;



}




void test2() {
    z3::context c;
    sv::symbolic<true, 32, Z3_BV_SORT > s32t(c, -5);
    sv::symbolic<true, 16, Z3_BV_SORT > s16t(c, -5);

    rsval<int>  hjk1(c, 8);
    rsval<int>  hjk2(c, 8);
    rsval<int>  sss1(s32t);
    rsval<short>  sss2(s16t);
    rsval<bool>  bo1(c, false);
    rsval<bool>  bo2(c, true);
    

    std::cout << hjk1 + hjk2 << std::endl;
    std::cout << hjk1 + sss1 << std::endl;
    std::cout << hjk1 + sss2 + -1ull << std::endl;


    std::cout << hjk1 + 45 - 67 / 54 * 66 + sss2 + -1ull << std::endl;

    std::cout << (hjk1 + sss2 << 56u) << std::endl;
    std::cout << ((((((sss2 + hjk1 >> 5u)) * 5 % 8 | 90) & 56ll) > 8989) && bo1 || bo2) << std::endl;

    std::cout << sss2.concat(hjk1) << std::endl;
    std::cout << sss2.extract<8, 6>() << std::endl;
    std::cout << hjk1.extract<7, 2>() << std::endl;


    //std::cout << (hjk1 + sss2 << 1ull) << std::endl;
    //std::cout << (hjk1 + sss2 >> 1ull) << std::endl;












    sv::symbolic<true, 32, Z3_BV_SORT > d2(c, -5);
    sv::symbolic<false, 32, Z3_BV_SORT > d3(c, -5);



    sv::symbolic<false, 16, Z3_BV_SORT > d4(c, (UShort)-5);

    __m128i sd = _mm_setr_epi32(1, 2, 3, 4);
    sv::symbolic<true, 72, Z3_FLOATING_POINT_SORT > f10_62(c, sd, sv::fpa_sort(c, 10, 62));





    tval tv4 = d4;

    fpval<16>& fa = (fpval<16>&) tv4;

    std::cout << fa << std::endl;

    sbool sb(c, false);
    sbool sb2(c, false);

    sv::sort rm = sv::fpRM(c, Irrm_NegINF);
    auto f1 = f10_62.fpa2fpa<5, 6>(rm);

    auto x1 = d2 + 8;
    auto x2 = d3 + 8;
    auto x3 = d2 + d3;
    auto x4 = d3 + d2;
    auto x5 = d4 + d2;
    auto x6 = d4 + d3;
    auto x7 = d2 + d4;
    auto x8 = d3 + d4;

    std::cout << f1 << std::endl;
    std::cout << f10_62 << std::endl;
    std::cout << f10_62.tobv().simplify() << std::endl;
    std::cout << d2 << std::endl;



    sv::symbolic<false, 240, Z3_BV_SORT > ug240(c, c.bv_const("ug240", 240));
    sv::symbolic<true, 240, Z3_BV_SORT > sg240(c, c.bv_const("sg240", 240));
    sv::symbolic<true, 32, Z3_BV_SORT > sg32(c, c.bv_const("sg32", 32));
    std::cout << ug240 << std::endl;
    std::cout << (sb ^ sb2) << std::endl;

    uint64_t UI64 = 1;
    uint32_t UI32 = 1;
    int64_t I64 = -2;
    uint32_t u32 = 2;
    int32_t I32 = -2;


    auto dd = I64 + UI32;
    auto dd2 = I64 + UI64;

    auto div1 = I64 / u32;//idiv  u32->I64
    auto div2 = UI32 / I64;// idiv  UI32->I64
    auto div3 = UI64 / I32;//div   I32->UI64
    auto div4 = UI32 / UI64;// div 

    auto div5 = UI64 / I64;// div 
    auto div6 = I64 / UI64;// div 



    bool cmp64 = UI64 < I64;//true : ȡ���� UI64
    cmp64 = I32 > UI32;

    cmp64 = UI64 < I32;//true : ȡ���� UI64
    cmp64 = I32 > UI64;

    cmp64 = I64 > UI64;//true
    cmp64 = I64 > UI32;//false




    cmp64 = UI32 < I64;//false : ȡ���� I64
    cmp64 = UI32 < I32;//true : ȡ���� UI32




    std::cout << (ug240 > -1ull) << std::endl;
    std::cout << (ug240 < -1) << std::endl;


    std::cout << (sg32 > -1ull) << std::endl;
    std::cout << (sg32 < -1) << std::endl;
    std::cout << (sg32 < -1ll) << std::endl;

    std::cout << (sg240 > 1ull) << std::endl;
    std::cout << (sg240 > 1) << std::endl;
    std::cout << (sg240 < -1) << std::endl;

    sv::symbolic<true, 233, Z3_BV_SORT > d233(c, c.bv_const("sg233", 233));
    sv::symbolic<false, 233, Z3_BV_SORT > ud233(c, c.bv_const("ug233", 233));
    std::cout << (ug240 >= d233) << std::endl;
    std::cout << (sg240 >= d233) << std::endl;
    std::cout << (sg240 > ud233) << std::endl;



}



    //cbool b1(c, 8);
    //sv::ctype_val<const bool> b2(c, 8);
    //x1 = 8;

    //x1 = x1 + x2;
    //auto add1 = x1 + 88;
    //std::cout << z3::expr(c, add1) << std::endl;

    //bv = x1;
    //bv = b1;


    //sval<8> s8_0(c, 88);
    //auto add2 = s8_0 + 88;
    //add2 = 78 + s8_0;

    //std::cout << z3::expr(c, add2) << std::endl;

    //uval<8> u8_0(c, 8);
    //sbool b3(c, false);
    //sbool b4(c, true);


    //sval<32> s32_0(c, 88);

    //bv = s32_0;

    //__m256i m256i;
    //__m256 m256;
    //sval<256> s256_0(c, m256i);
    //sval<256> s256_1(c, m256);

    //std::cout << z3::expr(c, s256_0) << std::endl;


    //sval<32> s32_1(c, (char)-1);

    //uval<16> u16_0(c, 8ull);
    //sval<16> s16_0(c, 8);
    //uval<32> u32_0(c, 8);
    //uval<64> u64_0(c, 8);
    //sval<64> s64_0(c, 8);
    ////auto v1 = b3 || b4;


    //char charvalue = -2;
    //sval<32> s32_2(c, charvalue);
    //uval<32> u32_2(c, charvalue);

    //std::cout << z3::expr(c, s32_1) << std::endl;
    //std::cout << z3::expr(c, u32_0) << std::endl;
    //std::cout << z3::expr(c, s32_2) << std::endl;
    //std::cout << z3::expr(c, u32_2) << std::endl;

    //auto v2 = u32_0 + s16_0;
    //std::cout << z3::expr(c, s16_0) << std::endl;
    //std::cout << z3::expr(c, v2) << std::endl;
    //auto df0 = u16_0 + s32_0;


    //auto dd = ite(u32_0 != s16_0, s32_1>>6, s32_0);

    //std::cout << z3::expr(c, dd) << std::endl;
    //auto df1 = g4 + g2;
    //auto df2 = g33 + g2;







//
//State_Tag success_ret(Kernel* _s) {
//    vex_printf("success_ret  ??????????\n\n%d");
//    return (State_Tag)0x999;
//
//    s->solv.push();
//    auto ecx = s->regs.Iex_Get<Ity_I32>(12);
//    auto edi = s->regs.Iex_Get<Ity_I32>(36);
//
//    for (int i = 0; i < 44; i++) {
//        auto al = s->mem.Iex_Load<Ity_I8>(ecx + i);
//        auto bl = s->mem.Iex_Load<Ity_I8>(edi + i);
//        s->solv.add(al == bl);
//    }
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("sat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    return Death;
//}
//
//
//State_Tag success_ret2(State* s) {
//
//    s->solv.push();
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("sat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    exit(1);
//    return Death;
//}
//
//




State_Tag success_ret3(State<Addr64>* s) {
    s->solv.push();
    UChar bf[] = { 0xEC, 0x29, 0xE3, 0x41, 0xE1, 0xF7, 0xAA, 0x1D, 0x29, 0xED, 0x29, 0x99, 0x39, 0xF3, 0xB7, 0xA9, 0xE7, 0xAC, 0x2B, 0xB7, 0xAB, 0x40, 0x9F, 0xA9, 0x31, 0x35, 0x2C, 0x29, 0xEF, 0xA8, 0x3D, 0x4B, 0xB0, 0xE9, 0xE1, 0x68, 0x7B, 0x41 };

    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RDI);
    for (int i = 0; i < 38; i++) {
        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
        s->solv.add(e == (UChar)bf[i]);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == z3::sat) {
        vex_printf("issat");
        auto m = s->solv.get_model();
        std::cout << m << std::endl;
        exit(0);
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    
    s->solv.pop();
    return Death;
}
//
//
//State_Tag success_ret33(State* s) {
//    s->solv.push();
//    UChar bf[] = { 133, 67, 104, 133, 245, 38, 60, 61, 39, 245, 51, 104, 62, 60, 118, 38, 245, 118, 165, 245, 19, 165, 61, 245, 62, 165, 45, 61, 245, 7, 60, 118, 29, 60, 15, 0, 133, 169 };
//
//    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rax);
//    for (int i = 0; i < 38; i++) {
//        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
//        s->solv.add(e == (UChar)bf[i]);
//    }
//    vex_printf("checking\n\n");
//    auto dfdfs = s->solv.check();
//    if (dfdfs == sat) {
//        vex_printf("issat");
//        auto m = s->solv.get_model();
//        std::cout << m << std::endl;
//        exit(0);
//    }
//    else {
//        vex_printf("unsat??????????\n\n%d", dfdfs);
//    }
//    s->solv.pop();
//    return Death;
//}
//
//
//State_Tag whil(State* s) {
//    return (State_Tag)0x233;
//}
//
//State_Tag pp(State* s) {
//    auto al = s->regs.Iex_Get<Ity_I32>(AMD64_IR_OFFSET::eax);
//    std::cout << Z3_ast_to_string(al, al) << std::endl;
//    s->regs.Ist_Put(AMD64_IR_OFFSET::rax, 38ull);
//    s->hook_pass(5);
//    return (State_Tag)Running;
//}
//
//State_Tag Dea(State* s) {
//    return (State_Tag)Death;
//}



#include "engine/guest_layout_helper.h"

Vns flag_limit(Vns& flag) {
    char flags_char[] = "@_-{}1:() ^";
    Vns re = Vns(flag, flags_char[0]) == flag;
    for (int i = 1; i < sizeof(flags_char); i++) {
        re = re || (Vns(flag, flags_char[i]) == flag);
    }
    auto ao1 = flag >= 'a' && flag <= 'z';
    auto ao2 = flag >= 'A' && flag <= 'Z';
    auto ao3 = flag >= '0' && flag <= '9';
    return re || ao1 || ao2 || ao3;
}



State_Tag test_ir_dirty_hook(State<Addr32>& state) {
    UInt esp = 0x8000 - 532;
    PWOW64_CONTEXT ContextRecord = (PWOW64_CONTEXT)(esp - sizeof(WOW64_CONTEXT));
    PEXCEPTION_RECORD32 ExceptionRecord = (PEXCEPTION_RECORD32)(esp - sizeof(WOW64_CONTEXT) - sizeof(EXCEPTION_RECORD32));

    if ((UInt)state.vex_stack_get(1) != (Addr32)(ULong)ContextRecord) return Death;
    if ((UInt)state.vex_stack_get(2) != EXCEPTION_BREAKPOINT) return Death;
    if ((UInt)state.vex_stack_get(22 + offsetof(WOW64_CONTEXT, Esp) / 4) != 0x8000) return Death;
    return Exit;
}

bool test_ir_dirty() {
    ctx32 v(VexArchX86, "");
    v.set_system(windows);
    v.param().set("ntdll_KiUserExceptionDispatcher", 0x2000);

    SP::win32 state(v, 0, True);
    state.setFlag(CF_traceJmp);
    state.setFlag(CF_ppStmts);
    state.mem.map(0x1000, 0x2000);
    state.mem.map(0x5000, 0x5000);
    state.hook_add(0x2000, test_ir_dirty_hook);
    state.mem.Ist_Store(0x1000, 0xcc);

    state.regs.Ist_Put(X86_IR_OFFSET::ESP, 0x8000);
    state.regs.Ist_Put(X86_IR_OFFSET::EIP, 0x1000);
    state.regs.Ist_Put(X86_IR_OFFSET::CC_OP, 0x0);


    state.start(0x1000);

    return state.status() == Exit;
}

bool creakme();
bool asong();


bool test_cmpress() {
    ctx64 v(VexArchAMD64, "");
    SP::linux64 state(v, 0, True);

    state.mem.map(0x602000, 0x2000);
    state.mem.map(0x5000, 0x5000);

    for (int i = 0; i < 4; i++) {
        SP::linux64* s = (SP::linux64*)(state.ForkState(20));
        Vns f1 = s->m_ctx.bv_const("a1", 8);
        Vns f2 = s->m_ctx.bv_const("a2", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->mem.Ist_Store(0x602080, 1000 + i);
        s->mem.Ist_Store(0x602088, 1000 + i);
        if (i == 3)
            s->set_status(Death);
    }
    std::cout << state << std::endl;
    for (int i = 4; i < 5; i++) {
        SP::linux64* s = (SP::linux64*)(state.ForkState(32));
        Vns f1 = s->m_ctx.bv_const("aj", 8);
        Vns f2 = s->m_ctx.bv_const("ak", 8);
        s->solv.add_assert(f1 > i);
        s->solv.add_assert(f2 < i);
        s->set_status((State_Tag)88);
    }

    std::cout << state << std::endl;
    UInt i = 0;
    for (auto s : state.branch) {
        i += 1;
        if (i <= 3) { continue; }
        SP::linux64* s2 = (SP::linux64*)(s->ForkState(20));
        s->set_status(Fork);
        Vns f = s2->m_ctx.bv_const("b", 8);
        s2->solv.add_assert(f > i);
        s2->mem.Ist_Store(0x602080, 100 + i);
        s2->mem.Ist_Store(0x602081, 100ull + i + (1ull << 63));
        if (i <= 4)
            continue;
        s2->m_InvokStack.push(787, 87);
    }


    std::cout << state << std::endl;


    cmpr::Context64 c = state.cmprContext(20, NewState);
    c.add_avoid(Death);
    c.add_avoid((State_Tag)88);

    state.compress(c);
    std::cout << state << std::endl;
    return true;
}


bool test_dirty_cmpress() {
    ctx64 v(VexArchAMD64, PROJECT_DIR"PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.xml");
    SP::linux64 state(v, 0, True);


    UChar bf[] = { 0xD9 ,0x74 ,0x24 ,0xE2 };
    for (int i = 0; i < sizeof(bf); i++) {
        state.mem.Ist_Store(state.get_cpu_ip() + i, bf[i]);
    }
    Vns f = state.m_ctx.bv_const("b", 64);
    state.solv.add_assert(f != 0);
    state.regs.Ist_Put(AMD64_IR_OFFSET::FPTAG, f);
    state.start();

    std::cout << state << std::endl;
    return true;
}



int main() {
    test1();
    test2();

    //testz3();
    //IR_TEST(test_ir_dirty);
    IR_TEST(creakme);
    IR_TEST(asong);
    IR_TEST(test_cmpress);

}

//int main() {
//    {
//        flag_max_count = 38+6;
//        flag_count = 0;
//
//        StatePrinter<StateAMD64> state(INIFILENAME, 0, True);
//        state.hook_add(0x400CC0, success_ret3);
//        StateAnalyzer gv(state);
//        gv.Run();
//    };
//    return 0;
//}

//
//int main() {
//    flag_max_count = 1;
//    flag_count = 0;
//
//    StatePrinter<StateX86> state(INIFILENAME, 0, True);
//
//    context& c = state;
//
//    for (int i = 0; i < 32; i++) {
//        auto flag = state.get_int_const(8);
//        auto ao1 = flag >= 'a' && flag <= 'f';
//        auto ao3 = flag >= '0' && flag <= '9';
//        state.mem.Ist_Store(i + 0x0019F554, flag);
//        state.add_assert(ao1 || ao3, 1);
//        if (i == 31) {
//            _VexGuestX86State reg(state);
//            state.mem.Ist_Store(reg.guest_EBP-0x24, flag);
//        }
//    }
//
//
//    state.hook_add(0x4050B0, Dea);
//    state.hook_add(0x4050D0, success_ret2);
//
//    State::pushState(state);
//    State::pool->wait();
//
//    return 0;
//}


//

