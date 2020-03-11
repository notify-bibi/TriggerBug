#pragma once
#ifndef _VEX_CONTEXT_
#define  _VEX_CONTEXT_
#include "tinyxml2/tinyxml2.h"
#include "thread_pool/thread_pool.h"
#include "engine/engine.h"
#include "state_class.h"


namespace TR {

    template<typename _> class vex_context;
    class vex_info;

    typedef State_Tag(*Hook_CB)(void*/*obj*/);
    //得到的ast无需Z3_inc_ref
    typedef Z3_ast(*TableIdx_CB)(void*/*obj*/, Addr64 /*base*/, Z3_ast /*idx*/);

    typedef struct _Hook_ {
        Hook_CB         cb;
        UInt            nbytes;
        __m64           original;
        TRControlFlags  cflag;
    }Hook_struct;


    class vctx_base {
        friend class vex_info;
        template<typename _> friend class State;
        template<typename _> friend class MEM;
        std::atomic_uint32_t m_user_counter = 1;
        UInt mk_user_id() { vassert(m_user_counter < -1u);  return m_user_counter++; }
        vctx_base() {}
    };

    class vex_info: public vctx_base {
        tinyxml2::XMLDocument doc;
        tinyxml2::XMLError err;
        tinyxml2::XMLElement* doc_TriggerBug;
        ULong trtraceflags;
    public:
        Int iropt_level;
        UInt guest_max_insns;
        VexRegisterUpdates iropt_register_updates_default;
        VexArch	guest;
        TR::GuestSystem guest_system;
        const char* MemoryDumpPath;
        tinyxml2::XMLElement* doc_VexControl;
        tinyxml2::XMLElement* doc_debug;
        UInt MaxThreadsNum;
        Int traceflags;
        IRConst bpt;
        ThreadPool m_pool;
        vex_info(const char* filename);
        UInt gRegsIpOffset() const;
        static void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk, VexArch guest, Int traceflags);
        void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk) { init_vta_chunk(vta_chunk, vge_chunk, guest, traceflags); }
        inline ULong getFlags() const { return trtraceflags; }
        IRConst const* softwareBptConst() const { return &bpt; };
        void softwareBptStore(UChar* dst) { memcpy(dst, &bpt.Ico.U8, IRConstTag2nb(bpt.tag)); };
        virtual UInt bit_wide() { VPANIC("??"); }

        inline operator vex_context<Addr32>& () { return *this; };
        inline operator vex_context<Addr64>& () { return *this; };
        inline operator vex_context<Addr32>* () { return reinterpret_cast <vex_context<Addr32>*>(this); };
        inline operator vex_context<Addr64>* () { return reinterpret_cast <vex_context<Addr64>*>(this); };

    private:

        tinyxml2::XMLError loadFile(const char* filename);
        void _gGuestArch();
        void _gMemoryDumpPath();
        void _gVexArchSystem();
        void _giropt_register_updates_default();
        void _giropt_level();
        void _gguest_max_insns();
        UInt _gMaxThreadsNum();
        void _gtraceflags();
        void _vex_info_init(const char* filename);
        IRConst _softwareBpt();
    };


    template<typename ADDR>
    class vex_context :public vex_info
    {
        State<ADDR>*    m_top_state;
        //模拟软件断点 software backpoint callback
        std::hash_map<Addr64, Hook_struct> m_callBackDict;
        std::hash_map<Addr64/*static table base*/, TableIdx_CB> m_tableIdxDict;

        vex_context(vex_context const&) = delete;
        void operator = (vex_context const&) = delete;
        void set_top_state(State<ADDR>* s) { vassert(!m_top_state); m_top_state = s; }
    public:
        vex_context(const char* filename) :vex_info(filename), m_top_state(nullptr) {};
        //backpoint add
        void hook_add(ADDR addr, State_Tag(*_func)(State<ADDR>*), TRControlFlags cflag);

        bool get_hook(Hook_struct& hs, ADDR addr);

        void hook_del(ADDR addr);

        inline ThreadPool& pool() { return m_pool; };


        /*read static_table from symbolic address  定义 index 和 该常量数组 之间的关系 不然只能逐一爆破 如DES的4个静态表
        表映射 callback

            模拟程序有静态的数组
                UInt staticMagic[256]（bss）;

            隐含关系为：
                For i in 0-255
                    staticMagic[i] = unknownFx()

            假如有如下加密方式：
                const UInt staticMagic[256]={xx,xx,xx,...,xx};

                UChar passwd[4] = input(4);
                UInt enc = staticMagic[passwd[0]]^staticMagic[passwd[1]]^staticMagic[passwd[2]]^staticMagic[passwd[3]]
                IF enc == encStatic:
                    print("ok")
                ELSE:
                    print("faild")
            当求解这种表达式时在原理上是解不开的，需要您显式进行定义staticMagic的index与staticMagic[index]的转换关系（否则需要爆破255^4）
            所以请使用idx2Value_Decl_add添加回调函数，当模拟执行时访问staticMagic，回调函数被调用
        */
        void idx2Value_Decl_add(Addr64 addr, Z3_ast(*_func) (State<ADDR>*, Addr64 /*base*/, Z3_ast /*idx*/)) { m_tableIdxDict[addr] = (TableIdx_CB)_func; };
        void idx2Value_Decl_del(Addr64 addr) { m_tableIdxDict.erase(m_tableIdxDict.find(addr)); };

        UInt bit_wide() override { return (UInt)((sizeof(ADDR))<<3); }
    };

    using ctx32 = vex_context<Addr32>;
    using ctx64 = vex_context<Addr64>;

};






#endif