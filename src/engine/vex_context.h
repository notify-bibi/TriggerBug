#pragma once
#ifndef _VEX_CONTEXT_
#define  _VEX_CONTEXT_
#include "thread_pool/thread_pool.h"
#include "engine/engine.h"

UInt gMaxThreadsNum();

namespace TR {
    template<typename ADDR>
    class MEM;
    template<unsigned int MAX_TMP>
    class EmuEnvironment;
    template<typename ADDR>
    class StateMEM;
    template<typename ADDR>
    class State;
    class TRsolver;

    typedef enum :unsigned int {
        NewState = 0,
        Running,
        Fork,
        Death,
        Exit,
        NoDecode,
        Exception,
        Dirty_ret
    }State_Tag;

    typedef enum :UChar {
        unknowSystem = 0b00,
        linux,
        windows
    }GuestSystem;


    typedef enum :ULong {
        CF_None = 0,
        CF_ppStmts = 1ull,
        CF_traceJmp = 1ull << 1,
        CF_traceState = 1ull << 2,
        CF_TraceSymbolic = 1ull << 3,
        CF_PassSigSEGV = 1ull << 4,
    }TRControlFlags;

}
namespace TR {

    class vex_info;
    class vctx_base;
    template<typename _> class vex_context;

    typedef State_Tag(*Hook_CB)(void*/*obj*/);
    //得到的ast无需Z3_inc_ref
    typedef Z3_ast(*TableIdx_CB)(void*/*obj*/, Addr64 /*base*/, Z3_ast /*idx*/);

    typedef struct _Hook_ {
        Hook_CB         cb;
        UInt            nbytes;
        __m64           original;
        TRControlFlags  cflag;
    }Hook_struct;


    class vex_info{
        friend class vctx_base;
        const char* m_bin;
        VexArch	m_guest;
        Int   m_iropt_level;
        UInt  m_guest_max_insns;
        VexRegisterUpdates m_iropt_register_updates_default;
        GuestSystem m_guest_system;
        ULong m_traceflags;
        UInt  m_maxThreadsNum;
        IRConst m_bpt_code;
        UInt m_IRoffset_IP, m_IRoffset_SP;

        vex_info(VexArch guest, const char* filename);
    public:
        static void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk, VexArch guest, ULong traceflags);
        void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk) { init_vta_chunk(vta_chunk, vge_chunk, m_guest, m_traceflags); }
        inline void set_system(GuestSystem s) { m_guest_system = s; }
        inline ULong getFlags() const { return m_traceflags; }
        inline ULong setFlag(ULong f) { return m_traceflags |= f; }
        inline ULong delFlag(ULong f) { return m_traceflags &= ~f; }
        inline ULong setFlag(TRControlFlags f) { return m_traceflags |= f; }
        inline ULong delFlag(TRControlFlags f) { return m_traceflags &= ~f; }
        IRConst const* softwareBptConst() const { return &m_bpt_code; };
        void softwareBptStore(UChar* dst) { memcpy(dst, &m_bpt_code.Ico.U8, IRConstTag2nb(m_bpt_code.tag)); };
        //必须保留一个virtual
        virtual UInt bit_wide() { VPANIC("??"); }
        static UInt gMaxThreadsNum();
        static IRConst gsoftwareBpt(VexArch guest);
        static Int gRegsIpOffset(VexArch guest);
        static Int gRegsSPOffset(VexArch guest);
        inline const char* gbin() const { return m_bin; }
        VexRegisterUpdates gRegisterUpdates() const { return m_iropt_register_updates_default; };
        inline VexArch gguest()const { return m_guest; }
        inline Int giropt_level() const { return m_iropt_level; }
        inline UInt gmax_insns() const { return m_guest_max_insns; }
        inline GuestSystem gguest_system() const { return m_guest_system; }
        inline UInt gmax_threads_num() const { return m_maxThreadsNum; }
        inline ULong gtraceflags() const { return m_traceflags; }
        inline UInt gRegsIpOffset() const { return m_IRoffset_IP; }
        inline UInt gRegsSpOffset() const { return m_IRoffset_SP; }

        inline operator vex_context<Addr32>& () const { return *reinterpret_cast <vex_context<Addr32>*>(const_cast<vex_info*>(this)); };
        inline operator vex_context<Addr64>& () const { return *reinterpret_cast <vex_context<Addr64>*>(const_cast<vex_info*>(this)); };
        inline operator vex_context<Addr32>* () const { return reinterpret_cast <vex_context<Addr32>*>(const_cast<vex_info*>(this)); };
        inline operator vex_context<Addr64>* () const { return reinterpret_cast <vex_context<Addr64>*>(const_cast<vex_info*>(this)); };
        inline operator vctx_base& () const { return *reinterpret_cast<vctx_base*>(const_cast<vex_info*>(this)); };
        inline operator vctx_base* () const { return reinterpret_cast<vctx_base*>(const_cast<vex_info*>(this)); };

    };



    class vctx_base : public vex_info {
        friend class vex_info;
        template<typename _> friend class State;
        template<typename _> friend class MEM;
        template<typename _> friend class vex_context;
        ThreadPool m_pool;
        std::atomic_uint32_t m_user_counter = 1;
        UInt mk_user_id() { vassert(m_user_counter < -1u);  return m_user_counter++; }
        vctx_base(VexArch guest, const char* filename):vex_info(guest, filename), m_pool(gmax_threads_num()){}
        ThreadPool& pool() { return m_pool; }

        inline operator vex_context<Addr32>& () { return *this; };
        inline operator vex_context<Addr64>& () { return *this; };
        inline operator vex_context<Addr32>* () { return reinterpret_cast <vex_context<Addr32>*>(this); };
        inline operator vex_context<Addr64>* () { return reinterpret_cast <vex_context<Addr64>*>(this); };
    private:
    };


    template<typename ADDR>
    class vex_context :public vctx_base
    {
        friend class vex_info;
        friend class State<ADDR>;
        State<ADDR>*    m_top_state;
        //模拟软件断点 software backpoint callback
        std::hash_map<Addr64, Hook_struct> m_callBackDict;
        std::hash_map<Addr64/*static table base*/, TableIdx_CB> m_tableIdxDict;

        vex_context(vex_context const&) = delete;
        void operator = (vex_context const&) = delete;
        void set_top_state(State<ADDR>* s) { vassert(!m_top_state); m_top_state = s; }
        //backpoint add
        void hook_add(State<ADDR>&state, ADDR addr, State_Tag(*_func)(State<ADDR>&), TRControlFlags cflag);
    public:
        vex_context(VexArch guest, const char* filename) :vctx_base(guest, filename), m_top_state(nullptr) {};

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