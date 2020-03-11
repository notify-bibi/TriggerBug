#pragma once
#include "crypto_analyzer/analyzer.h"

class ana_des : public analyzer
{
    static z3::expr item(z3::expr const& exp, Int base);
    static inline z3::expr xtime(z3::expr const& s) { return (s << 1) ^ ((z3::lshr(s, 7)) * 0x1B); }
    static inline z3::expr xtime3(z3::expr const& s) { return xtime(s) ^ s; }

    Z3_ast dword_4062E0(Addr64, Z3_ast maddr);
    Z3_ast dword_4059E0(Addr64, Z3_ast maddr);
    Z3_ast dword_4055E0(Addr64, Z3_ast maddr);
    Z3_ast dword_4051E0(Addr64, Z3_ast maddr);
    static bool check();
};

