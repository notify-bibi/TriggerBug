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


#include "engine/tr_main.h"



UInt flag_count = 0;
UInt flag_max_count = 0;

using namespace TR;

State_Tag StateAMD64::Sys_syscall_linux() {
    Vns al = regs.Iex_Get<Ity_I8>(AMD64_IR_OFFSET::RAX);
    if (al.real()) {
        Vns rdi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RDI);
        Vns rdx = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RDX);
        Vns rsi = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RSI);
        switch ((UChar)al) {
        case 0:// //LINUX - sys_read
            if (rdi == 0) {
                for (ULong n = 0; n < rdx; n++) {
                    if (flag_count >= flag_max_count) {
                        mem.Ist_Store(rsi + n, '\n');
                    }
                    else {
                        Vns FLAG = mk_int_const(8);
                        mem.Ist_Store(rsi + n, FLAG);
                        auto ao1 = FLAG >= 'A' && FLAG <= 'Z';
                        auto ao2 = FLAG >= 'a' && FLAG <= 'z';
                        auto ao3 = FLAG >= '0' && FLAG <= '9';
                        solv.add_assert(ao1 || ao2 || ao3 || FLAG == '_' || FLAG == '{' || FLAG == '}', True);
                    }
                }
                regs.Ist_Put(AMD64_IR_OFFSET::RAX, rdx);
                flag_count += rdx;
                return Running;
            }
        case 1: {//LINUX - sys_write
            for (ULong n = 0; n < rdx; n++) {
                UChar chr = mem.Iex_Load<Ity_I8>(rsi + n);
                vex_printf("%c", chr);
            }
            regs.Ist_Put(AMD64_IR_OFFSET::RAX, rdx);
            return Running;
        }

        case 0x3: {//LINUX - sys_close
            vex_printf("system call: sys_close description:0x%x\n", rdi);
            regs.Ist_Put(AMD64_IR_OFFSET::RAX, 1);
            break;
        }
        case 0x5: {//LINUX - sys_newfstat
            vex_printf("system call: sys_newfstat\tfd:0x%x 	struct stat __user *statbuf:0x%x", (ULong)rdi, (ULong)rsi);
            regs.Ist_Put(AMD64_IR_OFFSET::RAX, 0ull);
            return Running;
        }

        case 0xC: {//LINUX - sys_brk
            ULong rbx = regs.Iex_Get<Ity_I64>(AMD64_IR_OFFSET::RBX);
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
            regs.Ist_Put(AMD64_IR_OFFSET::RAX, g_brk);
            return Running;
        }
        case 0x23: {//LINUX - sys_nanosleep
            vex_printf("system call: sys_nanosleep\n");
            return Running;
        }
        case 0xE7: {//LINUX - sys_Exit
            vex_printf("system call: sys_Exit\n");
            return Exit;
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