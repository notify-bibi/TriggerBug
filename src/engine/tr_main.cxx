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
rsval<ADDR> TR::vex_read(State<ADDR>& s, const rsval<ADDR>& addr, const rsval<ADDR>& len) {
    vassert(len.real());
    UInt size = len;
    std::string st;
    char buff[2];
    buff[1] = 0;
    UInt n;
    std::cout << "vex_read :[";
    for (n = 0; n < size && buff[0] != '\n'; n += 1) {
        buff[0] = getchar();
        s.mem.store(addr + n, buff[0]);
        st.append(buff);
    }
    std::cout << "]" << std::endl;
    return rsval<ADDR>(s.m_ctx, n);
}

template<typename ADDR>
void TR::vex_write(State<ADDR>& s, const rsval<ADDR>& addr, const rsval<ADDR>& len) {
    vassert(len.real());
    UInt size = len;
    std::string st;
    char buff[2];
    buff[1] = 0;
    for (UInt n = 0; n < size; n += 1) {
        auto chr = s.mem.load<Ity_I8>(addr + n);
        if (chr.real()) {
            buff[0] = chr;
            st.append(buff);
        }
        else {
            st.append(chr.str());
        }
    }
    std::cout << "vex_write :[" << st << "]" << std::endl;
}


template rsval<Addr32> TR::vex_read(State<Addr32>& s, const rsval<Addr32>& addr, const rsval<Addr32>& len);
template void TR::vex_write(State<Addr32>& s, const rsval<Addr32>& addr, const rsval<Addr32>& len);
template rsval<Addr64> TR::vex_read(State<Addr64>& s, const rsval<Addr64>& addr, const rsval<Addr64>& len);
template void TR::vex_write(State<Addr64>& s, const rsval<Addr64>& addr, const rsval<Addr64>& len);


rsval<Addr32> TR::StateX86::TEB()
{
    return dirty_call("x86g_use_seg_selector", x86g_use_seg_selector,
        { 
            regs.get<Ity_I32>(X86_IR_OFFSET::LDT),
            regs.get<Ity_I32>(X86_IR_OFFSET::GDT),
            regs.get<Ity_I16>(X86_IR_OFFSET::FS),
            rcval<Addr32>(m_ctx, (ULong)0)
        },
        Ity_I32).tors<false, 32>();
}

