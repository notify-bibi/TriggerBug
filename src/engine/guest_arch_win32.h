#pragma once
#ifndef _GUEST_ARCH_WIN32_HEAD_
#define _GUEST_ARCH_WIN32_HEAD_

#include "engine/tr_main.h"

namespace TR {

    class win32 : public StateX86 {
        friend class SP::StatePrinter<Addr32, win32>;
        win32(StateX86* father_state, Addr32 gse) :StateX86(father_state, gse) {};
    public:
        win32(vex_context<Addr32>& vex_info, Addr32 gse, Bool _need_record) :StateX86(vex_info, gse, _need_record) {
            avoid_anti_debugging();
        };

        void avoid_anti_debugging();
        State_Tag Sys_syscall() ;
        State_Tag Ijk_call(IRJumpKind kd) override;
        void cpu_exception(Expt::ExceptionBase const& e) override;
        Kernel* ForkState(Addr32 ges) override { return new win32(this, ges); };


    };

};

#endif