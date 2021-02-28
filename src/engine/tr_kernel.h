
/* ---------------------------------------------------------------------------------------
 *      Hex-Rays Decompiler project
 *      Copyright (c) 2019 Microsoft Corporation by notify-bibi@github, 2496424084@qq.com
 *      ALL RIGHTS RESERVED.
 *
 *      这是 TR::State 的派生类定义地，只允许 32 or 64 
 *
 * ---------------------------------------------------------------------------------------
 */


#ifndef _TRIGGERBUG_KERNEL_
#define _TRIGGERBUG_KERNEL_


#include "engine/state_explorer.h"
namespace TR {
    class State;
}

namespace Ke {
    class Windows;
    class Linux;
    class Darwin;
    class OS_Unknow;

    enum OS_Kernel_Kd
    {
        OSK_Unknow,
        OSK_Windows,
        OSK_Linux,
        OSK_Darwin
    };

    class Kernel {
        friend class Windows;
        friend class Linux;
        friend class Darwin;
        friend class OS_Unknow;
        using param_type = TR::sys_params<size_t>;
        // ntdll_KiUserExceptionDispatcher  p32
        OS_Kernel_Kd m_os_kind;
        param_type   m_params;
        Kernel(OS_Kernel_Kd kd) :m_os_kind(kd){  }
        Kernel(OS_Kernel_Kd kd, Kernel& father, TR::State& s) :m_os_kind(kd), m_params(){ }
        Kernel(const Kernel& r) = delete;
        void operator =(const Kernel& r) = delete;
    public:
        param_type& param() { return m_params; }
        inline OS_Kernel_Kd get_OS_Kind() { return m_os_kind; }
        virtual TR::State_Tag Ijk_call(TR::State& st, IRJumpKind kd) { return TR::Death; }
        virtual void cpu_exception(TR::State& st, Expt::ExceptionBase const& e) {}
        virtual void avoid_anti_debugging(TR::State& st) { }

        //inline z3::vcontext& ctx() { return m_state.ctx(); }
        //inline TR::vex_context& vctx() { return m_state.vctx(); }
        //inline TR::vex_info& vinfo() { return m_state.vinfo(); }
        //inline TR::TRsolver& solver() { return m_state.solver(); }

        virtual ~Kernel() {}
    };
};

namespace TR {
    std::shared_ptr<TR::sys_params_value> gen_kernel(Ke::OS_Kernel_Kd kd);
}



#endif //_TRIGGERBUG_KERNEL_
