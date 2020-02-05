#pragma once
#ifndef KERNEL_HEAD_DEF
#define KERNEL_HEAD_DEF

#include "../engine.hpp"
#include "Variable.hpp"
#include "Register.hpp"
#include "tinyxml2/tinyxml2.h"

class Vex_Info {
    static tinyxml2::XMLDocument doc;
    static tinyxml2::XMLError err;
    static tinyxml2::XMLElement* doc_TriggerBug;
public:
    Vex_Info() {}
    static bool is_mode_64();
    static Int iropt_level;
    static UInt guest_max_insns;
    static VexRegisterUpdates iropt_register_updates_default;
    static VexArch	guest;
    static GuestSystem guest_system;
    static const char* MemoryDumpPath;
    static tinyxml2::XMLElement* doc_VexControl;
    static tinyxml2::XMLElement* doc_debug;
    static UInt MaxThreadsNum;
    static Int traceflags;
    static UInt gRegsIpOffset();
    static void vex_info_init(const char* filename);
    static void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk, VexArch guest, Int traceflags);
    static void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk) { init_vta_chunk(vta_chunk, vge_chunk, guest, traceflags); }

private:

    static tinyxml2::XMLError loadFile(const char* filename);
    static void _gGuestArch();
    static void _gMemoryDumpPath();
    static void _gVexArchSystem();
    static void _giropt_register_updates_default();
    static void _giropt_level();
    static void _gguest_max_insns();
    static void _gMaxThreadsNum();
    static void _gtraceflags();

};

class TRsolver;

class Kernel : public Vex_Info {
    friend class State<Addr32>;
    friend class State<Addr64>;
    template<typename ADDR> friend class VexIRDirty;
    void* m_base;
    Kernel(void* stateptr) :m_ctx(), m_base(stateptr)
    {
    }
    Kernel(Kernel const& father_kernel, void* stateptr) : m_ctx(), m_base(stateptr)
    {
    };
public:
    TRcontext               m_ctx;

    //ģ������ϵ� software backpoint callback
    static std::hash_map<Addr64, Hook_struct> CallBackDict;
    static std::hash_map<Addr64/*static table base*/, TRtype::TableIdx_CB> TableIdxDict;
    static ThreadPool* pool;
    std::queue<Z3_ast> io_buff;
    Vns const& sys_read() {

    }

public:
    static Vns T_Unop(context& m_ctx, IROp, Vns const&);
    static Vns T_Binop(context& m_ctx, IROp, Vns const&, Vns const&);
    static Vns T_Triop(context& m_ctx, IROp, Vns const&, Vns const&, Vns const&);
    static Vns T_Qop(context& m_ctx, IROp, Vns const&, Vns const&, Vns const&, Vns const&);
    inline operator context& () { return m_ctx; }
    inline operator TRcontext& () { return m_ctx; }
    inline operator Z3_context() const { return m_ctx; }/*read static_table from symbolic address  ���� index �� �ó������� ֮��Ĺ�ϵ ��Ȼֻ����һ���� ��DES��4����̬��
    ��ӳ�� callback
    
        ģ������о�̬������
            UInt staticMagic[256]��bss��;

        ������ϵΪ��
            For i in 0-255
                staticMagic[i] = unknownFx()

        ���������¼��ܷ�ʽ��
            const UInt staticMagic[256]={xx,xx,xx,...,xx};

            UChar passwd[4] = input(4);
            UInt enc = staticMagic[passwd[0]]^staticMagic[passwd[1]]^staticMagic[passwd[2]]^staticMagic[passwd[3]]
            IF enc == encStatic:
                print("ok")
            ELSE:
                print("faild")
        ��������ֱ��ʽʱ��ԭ�����ǽⲻ���ģ���Ҫ����ʽ���ж���staticMagic��index��staticMagic[index]��ת����ϵ��������Ҫ����255^4��
        ������ʹ��idx2Value_Decl_add��ӻص���������ģ��ִ��ʱ����staticMagic���ص�����������
    */
    static inline void idx2Value_Decl_add(Addr64 addr, TRtype::TableIdx_CB func) { TableIdxDict[addr] = func; };
    static inline void idx2Value_Decl_del(Addr64 addr, TRtype::TableIdx_CB func) { TableIdxDict.erase(TableIdxDict.find(addr)); };
    Z3_ast idx2Value(Addr64 base, Z3_ast idx);
    Addr64 get_cpu_ip();
    operator TRsolver& ();

    inline operator State<Addr32>& () { return *this; };
    inline operator State<Addr64>& () { return *this; };
    inline operator State<Addr32>* () { return reinterpret_cast <State<Addr32>*>(m_base); };
    inline operator State<Addr64>* () { return reinterpret_cast <State<Addr64>*>(m_base); };

};



#endif

