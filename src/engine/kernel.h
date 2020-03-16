#pragma once
#ifndef KERNEL_HEAD_DEF
#define KERNEL_HEAD_DEF

#include "engine.h"
#include "engine/vex_context.h"
#include "variable.h"
#include "register.h"
z3::sort translateRM(z3::context&, IRRoundingMode);

class Kernel {
    friend class TR::State<Addr32>;
    friend class TR::State<Addr64>;
public:

    z3::vcontext        m_ctx;
    std::queue<Z3_ast>  io_buff;
private:
    TR::vex_info&           m_vex_info;
    template<typename ADDR> friend class VexIRDirty;
    Kernel(TR::vex_info& vex_info) :m_ctx(), m_vex_info(vex_info) {}
    Kernel(Kernel const& father_kernel) : m_ctx(), m_vex_info(father_kernel.m_vex_info) {};

public:

public:
    static Vns T_Unop(z3::context& m_ctx, IROp, Vns const&);
    static Vns T_Binop(z3::context& m_ctx, IROp, Vns const&, Vns const&);
    static Vns T_Triop(z3::context& m_ctx, IROp, Vns const&, Vns const&, Vns const&);
    static Vns T_Qop(z3::context& m_ctx, IROp, Vns const&, Vns const&, Vns const&, Vns const&);
    inline operator const z3::context& () const { return m_ctx; }
    inline operator const z3::vcontext& () const { return m_ctx; }
    inline operator const Z3_context() const { return m_ctx; }
    inline const z3::vcontext& ctx() const { return m_ctx; }
    inline Kernel& kernel() { return *this; }
    inline const TR::vex_info& info() const { return m_vex_info; }
    

    inline operator TR::State<Addr32>& () { return *this; };
    inline operator TR::State<Addr64>& () { return *this; };
    inline operator TR::State<Addr32>* () { return reinterpret_cast <TR::State<Addr32>*>(this); };
    inline operator TR::State<Addr64>* () { return reinterpret_cast <TR::State<Addr64>*>(this); };
    //必须存在至少一个virtual喔，不然上面4句转换就会产生错位
    virtual Addr64 get_cpu_ip() { return 0; };
private:


};



#endif

