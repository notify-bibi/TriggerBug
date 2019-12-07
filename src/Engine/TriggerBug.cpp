﻿/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    TriggerBug.cpp: 
Abstract:
    API list;
Author:
    WXC 2019-05-31.
Revision History:
--*/


//#undef _DEBUG
#define DLL_EXPORTS
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\TriggerBug-asong.xml"
#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\xctf-asong\\TriggerBug Engine\\asong.xml"
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\Roads\\Roads.xml"
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\TriggerBug\\PythonFrontEnd\\examples\\puzzle\\puzzle.xml"
//#define INIFILENAME "C:\\Users\\bibi\\Desktop\\reverse\\c++symbol\\childRE.xml"



#include "engine.hpp"
#define vpanic(...) printf("%s line %d",__FILE__,__LINE__); vpanic(__VA_ARGS__);

#include "Register.hpp"
#include "memory.hpp"
#include "SimulationEngine/State_class.hpp"
#include "SimulationEngine/State_analyzer.hpp"
#include "Z3_Target_Call/Guest_Helper.hpp"



UInt flag_count = 0;
UInt flag_max_count = 0;
extern "C" void dfd();


class StateX86 : public State {
public:
    StateX86(const char* filename, ADDR gse, Bool _need_record) :State(filename, gse, _need_record) {};
    StateX86(StateX86* father_state, ADDR gse) :State(father_state, gse) {};

    void cpu_exception() {
        UInt seh_addr = x86g_use_seg_selector(regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::ldt), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::gdt), regs.Iex_Get<Ity_I16>(X86_IR_OFFSET::fs).zext(16), 0);
        Vns seh = mem.Iex_Load<Ity_I32>(seh_addr);
        Vns next = mem.Iex_Load<Ity_I32>(seh);
        Vns seh_exception_method = mem.Iex_Load<Ity_I32>(seh + 4);
        status = Exception;
        std::cout << " SEH Exceptions at:" << std::hex << guest_start << " \nGoto handel:" << seh_exception_method << std::endl;
        guest_start = seh_exception_method;

        /*  esp & ebp  不正确的esp*/
        regs.Ist_Put(X86_IR_OFFSET::esp, seh);

        exit(2);
    }

    State_Tag Ijk_call(IRJumpKind kd) {
        switch (kd) {
        case Ijk_Sys_syscall:
            return Sys_syscall();
        default:
            vex_printf("guest address: %p . error jmp kind: ", guest_start);
            ppIRJumpKind(kd);
            vex_printf("\n");
        }
        return Death;
    }

    State_Tag Sys_syscall() {
        UChar rax = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::eax);
        ULong rdi = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::edi);
        ULong rdx = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::edx);
        ULong rsi = regs.Iex_Get<Ity_I64>(X86_IR_OFFSET::esi);
        return Death;
    }

    virtual State* ForkState(ADDR ges) {
        return new StateX86(this, ges);
    };

};


class StateAMD64 : public State {
    ULong g_brk = ALIGN(0x000000000060A000, 32);
public:
    StateAMD64(const char* filename, Addr64 gse, Bool _need_record) :
        State(filename, gse, _need_record)
    {
    };

    StateAMD64(StateAMD64* father_state, Addr64 gse) :
        State(father_state, gse)
    {
    };

    void cpu_exception() {
        UInt seh_addr = x86g_use_seg_selector(regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::ldt), regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::gdt), regs.Iex_Get<Ity_I16>(X86_IR_OFFSET::fs).zext(16), 0);
        Vns seh = mem.Iex_Load<Ity_I32>(seh_addr);
        Vns next = mem.Iex_Load<Ity_I32>(seh);
        Vns seh_exception_method = mem.Iex_Load<Ity_I32>(seh + 4);
        status = Exception;
        std::cout << " SEH Exceptions at:" << std::hex << guest_start << " \nGoto handel:" << seh_exception_method << std::endl;
        guest_start = seh_exception_method;

        /*  esp & ebp  不正确的esp*/
        regs.Ist_Put(X86_IR_OFFSET::esp, seh);

        exit(2);
    }

    State_Tag Ijk_call(IRJumpKind kd) {
        switch (kd) {
        case Ijk_Sys_syscall:
            switch (guest_system) {
            case linux:return Sys_syscall_linux();
            }
        default:
            vex_printf("guest address: %p . error jmp kind: ", guest_start);
            ppIRJumpKind(kd);
            vex_printf("\n");
        }
    }

    State_Tag Sys_syscall_linux() {
        Vns al = regs.Iex_Get<Ity_I8>(AMD64_IR_OFFSET::rax);
        if (al.real()) {
            Vns rdi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rdi);
            Vns rdx = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rdx);
            Vns rsi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rsi);
            switch ((UChar)al) {
            case 0:// //LINUX - sys_read
                if (rdi == 0) {
                    for (ULong n = 0; n < rdx; n++) {
                        if (flag_count >= flag_max_count) {
                            mem.Ist_Store(rsi + n, '\n');
                        }
                        else {
                            Vns FLAG = get_int_const(8);
                            mem.Ist_Store(rsi + n, FLAG);
                            auto ao1 = FLAG >= 'A' && FLAG <= 'Z';
                            auto ao2 = FLAG >= 'a' && FLAG <= 'z';
                            auto ao3 = FLAG >= '0' && FLAG <= '9';
                            add_assert(ao1 || ao2 || ao3, True);
                        }
                    }
                    regs.Ist_Put(AMD64_IR_OFFSET::rax, rdx);
                    flag_count += rdx;
                    return Running;
                }
            case 1: {//LINUX - sys_write
                for (ULong n = 0; n < rdx; n++) {
                    UChar chr = mem.Iex_Load<Ity_I8>(rsi + n);
                    vex_printf("%c", chr);
                }
                regs.Ist_Put(AMD64_IR_OFFSET::rax, rdx);
                return Running;
            }

            case 0x3: {//LINUX - sys_close
                vex_printf("system call: sys_close description:0x%x\n", rdi);
                regs.Ist_Put(AMD64_IR_OFFSET::rax, 1);
                break;
            }
            case 0x5: {//LINUX - sys_newfstat
                vex_printf("system call: sys_newfstat\tfd:0x%x 	struct stat __user *statbuf:0x%x", (ULong)rdi, (ULong)rsi);
                regs.Ist_Put(AMD64_IR_OFFSET::rax, 0ull);
                return Running;
            }

            case 0xC: {//LINUX - sys_brk
                ULong rbx = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rbx);
                vex_printf("system call: brk address:0x%x\n", rbx);
                ULong brk = rbx;
                if (brk) {
                    if (brk < g_brk) {
                        mem.unmap(brk, g_brk);
                        g_brk = ALIGN(brk, 32);
                    }
                    else if (brk == g_brk) {
                        mem.map(g_brk, g_brk + 0x21000);
                        g_brk = ALIGN(g_brk + 0x21000, 32);
                    }
                    else {
                        mem.map(g_brk, brk);
                        g_brk = ALIGN(brk, 32);
                    }
                }
                regs.Ist_Put(AMD64_IR_OFFSET::rax, g_brk);
                return Running;
            }
            case 0x23: {//LINUX - sys_nanosleep
                vex_printf("system call: sys_nanosleep\n");
                return Running;
            }
            case 0xE7: {//LINUX - sys_Exit
                vex_printf("system call: sys_Exit\n");
                return Death;
            }
            case 0x101: {//LINUX - sync_file_range
                // rsi filename   rdx flag
                std::stringstream filename;
                if (rsi.real()) {
                    UInt p = getStr(filename, rsi);
                    if (p == -1) {
                        vex_printf("system call: sync_file_range\tname:%s flag:0x%x", filename.str().c_str(), (ULong)rdx);

                        //result = state.file_system.sync_file_range(filename = filename, flags = rdx)
                        //setRax(state, result)
                    }
                }
                break;
            }

            }
            vex_printf("system call: sys_ %d\n", (UChar)al);
        }
       
        return Death;
    }

    State* ForkState(ADDR ges) {
        return new StateAMD64(this, ges);
    };
};









State_Tag success_ret(State* s) {
    vex_printf("success_ret  ??????????\n\n%d");
    return (State_Tag)0x999;

    s->solv.push();
    auto ecx = s->regs.Iex_Get<Ity_I32>(12);
    auto edi = s->regs.Iex_Get<Ity_I32>(36);

    for (int i = 0; i < 44; i++) {
        auto al = s->mem.Iex_Load<Ity_I8>(ecx + i);
        auto bl = s->mem.Iex_Load<Ity_I8>(edi + i);
        s->add_assert_eq(al, bl);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == sat) {
        vex_printf("sat");
        auto m = s->solv.get_model();
        std::cout << m << std::endl;
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    s->solv.pop();
    return Death;
}


State_Tag success_ret2(State* s) {

    s->solv.push();
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == sat) {
        vex_printf("sat");
        auto m = s->solv.get_model();
        std::cout << m << std::endl;
    }
    else {
        vex_printf("unsat??????????\n\n%d", dfdfs);
    }
    s->solv.pop();
    exit(1);
    return Death;
}


State_Tag success_ret3(State* s) {
    s->solv.push();
    UChar bf[] = { 0xEC, 0x29, 0xE3, 0x41, 0xE1, 0xF7, 0xAA, 0x1D, 0x29, 0xED, 0x29, 0x99, 0x39, 0xF3, 0xB7, 0xA9, 0xE7, 0xAC, 0x2B, 0xB7, 0xAB, 0x40, 0x9F, 0xA9, 0x31, 0x35, 0x2C, 0x29, 0xEF, 0xA8, 0x3D, 0x4B, 0xB0, 0xE9, 0xE1, 0x68, 0x7B, 0x41 };

    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rdi);
    for (int i = 0; i < 38; i++) {
        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
        s->add_assert(e == (UChar)bf[i], True);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == sat) {
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


State_Tag success_ret33(State* s) {
    s->solv.push();
    UChar bf[] = { 133, 67, 104, 133, 245, 38, 60, 61, 39, 245, 51, 104, 62, 60, 118, 38, 245, 118, 165, 245, 19, 165, 61, 245, 62, 165, 45, 61, 245, 7, 60, 118, 29, 60, 15, 0, 133, 169 };

    auto enc = s->regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::rax);
    for (int i = 0; i < 38; i++) {
        Vns e = s->mem.Iex_Load<Ity_I8>(enc + i);
        s->add_assert(e == (UChar)bf[i], True);
    }
    vex_printf("checking\n\n");
    auto dfdfs = s->solv.check();
    if (dfdfs == sat) {
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


State_Tag whil(State* s) {
    return (State_Tag)0x233;
}

State_Tag pp(State* s) {
    auto al = s->regs.Iex_Get<Ity_I32>(AMD64_IR_OFFSET::eax);
    std::cout << Z3_ast_to_string(al, al) << std::endl;
    s->regs.Ist_Put(AMD64_IR_OFFSET::rax, 38ull);
    s->hook_pass(5);
    return (State_Tag)Running;
}

State_Tag Dea(State* s) {
    return (State_Tag)Death;
}



#include "SimulationEngine/Z3_Target_Call/Guest_Helper.hpp"

Vns flag_limit(Vns &flag) {
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


#include "example.hpp"
 
//
//
//void test_apps() {
//    Z3_config cfg = Z3_mk_config();
//    Z3_set_param_value(cfg, "MODEL", "true");
//    Z3_context ctx = Z3_mk_context(cfg);
//    Z3_solver s = Z3_mk_solver(ctx);
//    Z3_solver_inc_ref(ctx, s);
//    Z3_symbol A = Z3_mk_string_symbol(ctx, "A");
//    Z3_symbol F = Z3_mk_string_symbol(ctx, "f");
//    Z3_sort SA = Z3_mk_uninterpreted_sort(ctx, A);
//    Z3_func_decl f = Z3_mk_func_decl(ctx, F, 1, &SA, SA);
//    Z3_symbol X = Z3_mk_string_symbol(ctx, "x");
//    Z3_ast x = Z3_mk_const(ctx, X, SA);
//    Z3_ast fx = Z3_mk_app(ctx, f, 1, &x);
//    Z3_ast ffx = Z3_mk_app(ctx, f, 1, &fx);
//    Z3_ast fffx = Z3_mk_app(ctx, f, 1, &ffx);
//    Z3_ast ffffx = Z3_mk_app(ctx, f, 1, &fffx);
//    Z3_ast fffffx = Z3_mk_app(ctx, f, 1, &ffffx);
//
//    Z3_ast fml = Z3_mk_not(ctx, Z3_mk_eq(ctx, x, fffffx));
//
//    Z3_solver_assert(ctx, s, fml);
//    Z3_lbool r = Z3_solver_check(ctx, s);
//    std::cout << r << "\n";
//    Z3_solver_dec_ref(ctx, s);
//    Z3_del_config(cfg);
//    Z3_del_context(ctx);
//}
//
//void test_bvneg() {
//    Z3_config cfg = Z3_mk_config();
//    Z3_set_param_value(cfg, "MODEL", "true");
//    Z3_context ctx = Z3_mk_context(cfg);
//    Z3_solver s = Z3_mk_solver(ctx);
//    Z3_solver_inc_ref(ctx, s);
//
//    {
//        Z3_sort bv30 = Z3_mk_bv_sort(ctx, 30);
//        Z3_ast  x30 = Z3_mk_fresh_const(ctx, "x", bv30);
//        Z3_ast fml = Z3_mk_eq(ctx, Z3_mk_int(ctx, -1, bv30),
//            Z3_mk_bvadd(ctx, Z3_mk_int(ctx, 0, bv30),
//                x30));
//        Z3_solver_assert(ctx, s, fml);
//        Z3_lbool r = Z3_solver_check(ctx, s);
//        std::cout << r << "\n";
//    }
//
//    {
//        Z3_sort bv31 = Z3_mk_bv_sort(ctx, 31);
//        Z3_ast  x31 = Z3_mk_fresh_const(ctx, "x", bv31);
//        Z3_ast fml = Z3_mk_eq(ctx, Z3_mk_int(ctx, -1, bv31),
//            Z3_mk_bvadd(ctx, Z3_mk_int(ctx, 0, bv31),
//                x31));
//        Z3_solver_assert(ctx, s, fml);
//        Z3_lbool r = Z3_solver_check(ctx, s);
//        std::cout << r << "\n";
//    }
//
//    {
//        Z3_sort bv32 = Z3_mk_bv_sort(ctx, 32);
//        Z3_ast  x32 = Z3_mk_fresh_const(ctx, "x", bv32);
//        Z3_ast fml = Z3_mk_eq(ctx,
//            Z3_mk_int(ctx, -1, bv32),
//            Z3_mk_bvadd(ctx, Z3_mk_int(ctx, 0, bv32),
//                x32));
//        Z3_solver_assert(ctx, s, fml);
//        Z3_lbool r = Z3_solver_check(ctx, s);
//        std::cout << r << "\n";
//    }
//
//    Z3_solver_dec_ref(ctx, s);
//    Z3_del_config(cfg);
//    Z3_del_context(ctx);
//}
//
//static bool cb_called = false;
//static void my_cb(Z3_context, Z3_error_code) {
//    cb_called = true;
//}
//
//static void test_mk_distinct() {
//    Z3_config cfg = Z3_mk_config();
//    Z3_context ctx = Z3_mk_context(cfg);
//    Z3_set_error_handler(ctx, my_cb);
//
//    Z3_sort bv8 = Z3_mk_bv_sort(ctx, 8);
//    Z3_sort bv32 = Z3_mk_bv_sort(ctx, 32);
//    Z3_ast args[] = { Z3_mk_int64(ctx, 0, bv8), Z3_mk_int64(ctx, 0, bv32) };
//    Z3_ast d = Z3_mk_distinct(ctx, 2, args);
//    //ENSURE(cb_called);
//    Z3_del_config(cfg);
//    Z3_del_context(ctx);
//
//}




int main() {
    {
        /*

        test_apps();
        test_bvneg();
        test_mk_distinct();
*/



        context c,c1,c2;
        solver ss(c);
        solver ss2(ss);
        /*{
            sort sor = c.bv_sort(63);
            expr bv8 = (c.constant("j", sor) + 445 - 6767) * 676;
        }*/

        flag_max_count = 1;
        flag_count = 0;

        StatePrinter<StateAMD64> state(INIFILENAME, (Addr64)0, True);
        context& m_ctx = state;



        /*  State::pool->enqueue(
              [&c, &c1, &bv8] {
                  for (int i = 0; i < 5000; i++) {
                      expr(c1, Z3_translate(c, bv8, c1));
                  };
              }
          );

          State::pool->enqueue(
              [&c, &c2, &bv8] {
                  for (int i = 0; i < 10000; i++) {
                      expr(c2, Z3_translate(c, bv8, c2));
                  };
              }
          );


          State::pool->wait();*/




        z3::params m_params(m_ctx);
        z3::tactic m_tactic(with(tactic(m_ctx, "simplify"), m_params) &
            tactic(m_ctx, "sat") &
            tactic(m_ctx, "solve-eqs") &
            tactic(m_ctx, "bit-blast") &
            tactic(m_ctx, "smt")
            &
            tactic(m_ctx, "factor") &
            tactic(m_ctx, "bv1-blast") &
            tactic(m_ctx, "qe-sat") &
            tactic(m_ctx, "ctx-solver-simplify") &
            tactic(m_ctx, "nla2bv") &
            tactic(m_ctx, "symmetry-reduce")/**/
        );
        //state.setSolver(m_tactic);


        TRGL::VexGuestAMD64State reg(state);
        for (int i = 0; i < 38; i++) {
            auto flag = state.get_int_const(8);
            auto ao3 = flag >= 1 && flag <= 128;
            state.mem.Ist_Store(reg.guest_RDI + i, flag);
            state.add_assert(ao3, 1);
            /*TESTCODE(
                eval_size = eval_all(guard_result, state.solv, flag);
            );*/
        }
        state.hook_add(0x000400E7A, pp);
       // state.hook_add(0x00400ED3, success_ret33);
        state.hook_add(0x400CC0, success_ret3);
        
        {
            StatePrinter<StateAMD64> state2(&state, 0x00400F7A);
            auto df = state2.get_int_const(64);
            state2.add_assert(df < 10, 1);
            state2.mem.Ist_Store(0x000400E7A + df, state2.get_int_const(8));
            state2.mem.Iex_Load<Ity_I64>(0x000400E7A);
            State::pushState(state2);
            State::pool->wait();
        }

        StateAnalyzer gv(state);
        gv.Run();
    };
    return 0;
}

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