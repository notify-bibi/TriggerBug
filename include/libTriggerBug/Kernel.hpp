#pragma once
#ifndef KERNEL_HEAD_DEF
#define KERNEL_HEAD_DEF

#include "engine.hpp"
#include "Variable.hpp"
#include "Register.hpp"
#include "tinyxml2/tinyxml2.h"

class Vex_Info {
    tinyxml2::XMLDocument doc;
    tinyxml2::XMLError err;
    tinyxml2::XMLElement* doc_TriggerBug;
    ULong trtraceflags;
public:
    Int iropt_level;
    UInt guest_max_insns;
    VexRegisterUpdates iropt_register_updates_default;
    VexArch	guest;
    GuestSystem guest_system;
    const char* MemoryDumpPath;
    tinyxml2::XMLElement* doc_VexControl;
    tinyxml2::XMLElement* doc_debug;
    UInt MaxThreadsNum;
    Int traceflags;
    IRConst bpt;
    Vex_Info(const char* filename) :
        doc(tinyxml2::XMLDocument()),
        iropt_register_updates_default(VexRegUpdSpAtMemAccess),
        iropt_level(2),
        guest_max_insns(100),
        err(tinyxml2::XML_ERROR_COUNT),
        doc_TriggerBug(nullptr),
        doc_VexControl(nullptr),
        doc_debug(nullptr),
        guest_system(unknowSystem),
        guest(VexArch_INVALID),
        MemoryDumpPath("你没有这个文件"),
        MaxThreadsNum(16),
        traceflags(0)
    {
        _vex_info_init(filename);
        bpt = _softwareBpt();
    }
    UInt gRegsIpOffset() const;
    static void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk, VexArch guest, Int traceflags);
    void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk) { init_vta_chunk(vta_chunk, vge_chunk, guest, traceflags); }
    inline ULong getFlags() const{ return trtraceflags; }
    IRConst const* softwareBptConst() const { return &bpt; };
    void softwareBptStore(UChar* dst) { memcpy(dst, &bpt.Ico.U8, IRConstTag2nb(bpt.tag)); };
private:

    tinyxml2::XMLError loadFile(const char* filename);
    void _gGuestArch();
    void _gMemoryDumpPath();
    void _gVexArchSystem();
    void _giropt_register_updates_default();
    void _giropt_level();
    void _gguest_max_insns();
    void _gMaxThreadsNum();
    void _gtraceflags();
    void _vex_info_init(const char* filename);
    IRConst _softwareBpt();
};




class TRsolver;

class Kernel {
    friend class State<Addr32>;
    friend class State<Addr64>;
public:
    static ThreadPool*  pool;
    TRcontext           m_ctx;
    std::queue<Z3_ast>  io_buff;
private:
    Vex_Info&           m_vex_info;
    template<typename ADDR> friend class VexIRDirty;
    Kernel(Vex_Info& vex_info) :m_ctx(), m_vex_info(vex_info)
    {
    }
    Kernel(Kernel const& father_kernel) : m_ctx(), m_vex_info(father_kernel.m_vex_info)
    {
    };

public:
    Vns const& sys_read() {

    }

public:
    static Vns T_Unop(z3::context& m_ctx, IROp, Vns const&);
    static Vns T_Binop(z3::context& m_ctx, IROp, Vns const&, Vns const&);
    static Vns T_Triop(z3::context& m_ctx, IROp, Vns const&, Vns const&, Vns const&);
    static Vns T_Qop(z3::context& m_ctx, IROp, Vns const&, Vns const&, Vns const&, Vns const&);
    inline operator const z3::context& () const { return m_ctx; }
    inline operator const TRcontext& () const { return m_ctx; }
    inline operator const Z3_context() const { return m_ctx; }
    inline const TRcontext& ctx() const { return m_ctx; }
    inline Kernel& kernel() { return *this; }
    inline const Vex_Info& info() const { return m_vex_info; }
    

    inline operator State<Addr32>& () { return *this; };
    inline operator State<Addr64>& () { return *this; };
    inline operator State<Addr32>* () { return reinterpret_cast <State<Addr32>*>(this); };
    inline operator State<Addr64>* () { return reinterpret_cast <State<Addr64>*>(this); };
    virtual Addr64 get_cpu_ip() { return 0; };//必须存在至少一个virtual喔，不然上面4句转换就会产生错位
private:


};



#endif

