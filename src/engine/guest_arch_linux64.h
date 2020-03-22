#pragma once
#ifndef _GUEST_ARCH_LINUX64_HEAD_
#define _GUEST_ARCH_LINUX64_HEAD_
#include "engine/tr_main.h"

namespace TR {
    class linux64 :public StateAMD64 {
        friend class SP::StatePrinter<Addr64, linux64>;
        ULong g_brk = ALIGN(0x0000000000603000, 64);
        linux64(StateAMD64* father_state, Addr64 gse) :StateAMD64(father_state, gse) {};
    public:
        linux64(vex_context<Addr64>& vex_info, Addr64 gse, Bool _need_record) :StateAMD64(vex_info, gse, _need_record) {
            avoid_anti_debugging();
        };

        void avoid_anti_debugging();
        State_Tag Sys_syscall();
        State_Tag Ijk_call(IRJumpKind kd) override;
        void cpu_exception(Expt::ExceptionBase const& e) override;
        Kernel* ForkState(Addr64 ges) override { return new linux64(this, ges); };
    };
};
#endif