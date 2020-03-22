/*++
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


using namespace TR;

template<typename ADDR>
Vns TR::vex_read(State<ADDR>& s, const Vns& addr, const Vns& len) {
    vassert(len.real());
    UInt size = len;
    std::string st;
    char buff[2];
    buff[1] = 0;
    UInt n;
    std::cout << "vex_read :[";
    for (n = 0; n < size && buff[0] != '\n'; n += 1) {
        buff[0] = getchar();
        s.mem.Ist_Store(addr + n, buff[0]);
        st.append(buff);
    }
    std::cout << "]" << std::endl;
    return Vns(s.m_ctx, n);
}

template<typename ADDR>
void TR::vex_write(State<ADDR>& s, const Vns& addr, const Vns& len) {
    vassert(len.real());
    UInt size = len;
    std::string st;
    char buff[2];
    buff[1] = 0;
    for (UInt n = 0; n < size; n += 1) {
        Vns chr = s.mem.Iex_Load<Ity_I8>(addr + n);
        if (chr.real()) {
            buff[0] = chr;
            st.append(buff);
        }
        else {
            st.append((std::string)chr);
        }
    }
    std::cout << "vex_write :[" << st << "]" << std::endl;
}


template Vns TR::vex_read(State<Addr32>& s, const Vns& addr, const Vns& len);
template void TR::vex_write(State<Addr32>& s, const Vns& addr, const Vns& len);
template Vns TR::vex_read(State<Addr64>& s, const Vns& addr, const Vns& len);
template void TR::vex_write(State<Addr64>& s, const Vns& addr, const Vns& len);


Vns TR::StateX86::TEB()
{
    return dirty_call("x86g_use_seg_selector", x86g_use_seg_selector,
        { 
            regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::LDT).zext(32),
            regs.Iex_Get<Ity_I32>(X86_IR_OFFSET::GDT).zext(32),
            regs.Iex_Get<Ity_I16>(X86_IR_OFFSET::FS).zext(16),
            Vns(m_ctx, (ULong)0)
        },
        Ity_I32);
}

