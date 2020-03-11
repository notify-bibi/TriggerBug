#pragma once
#ifndef _ANALYZER_
#define _ANALYZER_
#include "engine/tr_main.h"

class mem32;
class mem64;

class membase {
    friend class mem32;
    friend class mem64;
    membase(){}
public:
    virtual Vns read() { VPANIC("GG"); return Vns(); };
    virtual z3::context& ctx() { VPANIC("GG") return z3::context(); }
};

class mem32 : public membase {
    TR::MEM<Addr32>& m_mem;
public:
    mem32(TR::MEM<Addr32>& mem) :m_mem(mem) { }
    z3::context& ctx() override { return m_mem.ctx(); }
};

class mem64 : public membase {
    TR::MEM<Addr64>& m_mem;
public:
    mem64(TR::MEM<Addr64>& mem) : m_mem(mem) { }
    z3::context& ctx() override { return m_mem.ctx(); }
};

class analyzer : protected membase {
public:
    z3::context& m_ctx;
    Addr64 m_ana_addr;
    z3::expr m_offset;

    analyzer(TR::MEM<Addr32>& mem, Addr64 memaddr, z3::expr offset) :
        membase(mem32(mem)), m_ctx(mem), m_ana_addr(memaddr), m_offset(offset)
    {
    }

    analyzer(TR::MEM<Addr64>& mem, Addr64 memaddr, z3::expr offset) :
        membase(mem64(mem)), m_ctx(mem), m_ana_addr(memaddr), m_offset(offset)
    {
    }
public:
    z3::context& ctx() { return membase::ctx(); }
};





















#endif