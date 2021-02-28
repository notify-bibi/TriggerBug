#pragma once
#ifndef _VEX_CONTEXT_
#define  _VEX_CONTEXT_
#include "engine\engine.h"
#include "thread_pool\thread_pool.h"
#include "engine\basic_var.hpp"
#include <functional>

#include <cstdio>
#include "spdlog/spdlog.h"
#include "spdlog/cfg/env.h" // for loading levels from the environment variable
#include "engine/tr_ir_opt.h"



class IRSBCache;

namespace TR {

    class EmuEnvironment;
    class TRsolver;
    class StateBase;


    typedef enum :unsigned int {
        NewState = 0,
        Running,
        Fork,
        Death,
        Exit,
        NoDecode,
        Exception,
        DirtyRet,
        DirtyRecursiveExec //  dirty call -> dirty call is not support
    }State_Tag;



    typedef enum :ULong {
        CF_None = 0,
        CF_ppStmts = 1ull,
        CF_traceJmp = 1ull << 1,
        CF_traceState = 1ull << 2,
        CF_TraceSymbolic = 1ull << 3,
        CF_PassSigSEGV = 1ull << 4,
        CF_traceInvoke = 1ull << 5,
    }TRControlFlags;

}
namespace TR {

    class vex_info;
    class vctx_base;
    class StateBase;
    class State;
    class vex_context;



    // vex_info
    class vex_info{
        friend class vctx_base;
        VexArch	m_guest;
        Int   m_iropt_level;
        UInt  m_guest_max_insns;
        VexRegisterUpdates m_iropt_register_updates_default;
        ULong m_traceflags;
        UInt  m_maxThreadsNum;
        IRConst m_bpt_code;
        UInt m_IRoffset_IP, m_IRoffset_SP, m_IRoffset_BP;
        bool m_mode_32;

    public:
        vex_info(VexArch guest, Int iropt_level, UInt guest_max_insns, VexRegisterUpdates iropt_register_updates_default, ULong traceflags, UInt maxThreadsNum);
        vex_info(VexArch guest);
        ~vex_info();


        vex_info(const vex_info& v);
        void operator =(const vex_info& v);
        VexControl init_VexControl();
        VexArch enable_long_mode();
        VexArch disable_long_mode();
        static void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk, VexArch guest, ULong traceflags);
        void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk) { init_vta_chunk(vta_chunk, vge_chunk, m_guest, m_traceflags); }
        IRConst const* softwareBptConst() const { return &m_bpt_code; };
        void softwareBptStore(UChar* dst) { memcpy(dst, &m_bpt_code.Ico.U8, IRConstTag2nb(m_bpt_code.tag)); };

        static UInt gMaxThreadsNum();
        static IRConst gsoftwareBpt(VexArch guest);
        static Int gRegsIpOffset(VexArch guest);
        static Int gRegsSPOffset(VexArch guest);
        static Int gRegsBPOffset(VexArch guest);
        static Bool gis_mode_32(VexArch guest);

        VexRegisterUpdates gRegisterUpdates() const { return m_iropt_register_updates_default; };
        inline VexArch gguest()const { return m_guest; }
        inline Int giropt_level() const { return m_iropt_level; }
        inline UInt gmax_insns() const { vassert(m_guest_max_insns <= 0xffff); return m_guest_max_insns; }
        inline UInt gmax_threads_num() const { return m_maxThreadsNum; }
        inline ULong gtraceflags() const { return m_traceflags; }
        inline UInt gRegsIpOffset() const { return m_IRoffset_IP; }
        inline UInt gRegsSpOffset() const { return m_IRoffset_SP; }
        inline UInt gRegsBpOffset() const { return m_IRoffset_BP; }
        inline Bool is_mode_32() const { return m_mode_32; };

    };



    template<class T>
    class sys_params {
        HASH_MAP<std::string, T> m_symbols;
    public:
        sys_params(){}
        inline void set(const char* key, const T& value) {
            m_symbols[key] = value;
        }
        inline bool is_exist(const char* key) const { return m_symbols.find(key) != m_symbols.end(); }
        inline T& get(const char* key) { return m_symbols[key]; }
        sys_params(const sys_params&) = delete;
        void operator =(const sys_params&) = delete;
    };

    class sys_params_value {
        size_t m_value;
    public:
        sys_params_value(size_t value) :m_value(value) {  }  // inc_ref();
        virtual sys_params_value fork() { return sys_params_value(0); }
        virtual void delete_value() { m_value = 0; }
        virtual void inc_ref() { }
        virtual void dec_ref() { }
        inline size_t value() { return m_value; }
        sys_params_value(const sys_params_value& v) : sys_params_value(v.m_value) { }
        void operator =(const sys_params_value& v) { this->~sys_params_value(); new(this) sys_params_value(v); }
        virtual ~sys_params_value() { } // final ~class need call dec_ref()
    };


    // add some const info
    // topState tree 只有一个 vex_context
    // sys_params 用于功能扩展或者数据传递
    // vex_context: vctx_base
    class vctx_base {
        friend class StateBase;
        friend class vex_context;
        using paramType = sys_params<std::shared_ptr<sys_params_value>>;

        StateBase* m_top_state;
        ThreadPool m_pool;
        std::atomic_uint32_t m_user_counter;
        paramType m_params;

        UInt mk_user_id() { vassert(m_user_counter < -1u);  return m_user_counter++; }
        vctx_base(Int max_threads);
    public:
        paramType& param() { return m_params; }
        ThreadPool& pool() { return m_pool; }
        void set_top_state(StateBase* top_state) { m_top_state = top_state; }
        static UInt gMaxThreadsNum(Int max_threads);

        vctx_base(const vctx_base& r) = delete;
        void operator =(const vctx_base& r) = delete;
        virtual ~vctx_base() { m_pool.wait(); }
    };

    typedef State_Tag(*Hook_CallBack) (State&);

    typedef struct _Hook_ {
        Hook_CallBack   cb;
        TRControlFlags  cflag;
    }Hook_struct;


    // 一个 top state tree 只有一个 vex_context
    // vex_context: vctx_base
    class vex_context :public vctx_base
    {
    public:
        //读
        using Hook_Read =  rsval<Long>  (*)(StateBase&, const rsval<ULong>&, const rsval<Long>&);
        //写
        using Hook_Write = void(*)(StateBase&, const rsval<ULong>&, const rsval<Long>&);
        //idx2v
        using Hook_idx2Value = z3::expr(*) (StateBase&, HWord /*base*/, Z3_ast /*idx*/);
        

    private:
        vex_context(const vex_context& r) = delete;
        void operator =(const vex_context& r) = delete;
        //模拟软件断点 software backpoint callback
        HASH_MAP<Addr64, Hook_struct> m_callBackDict;
        HASH_MAP<Addr64/*static table base*/, Hook_idx2Value> m_tableIdxDict;
        void* m_hook_read;
        void* m_hook_write;
        IRSBCache* m_irsb_cache = nullptr;
    public:
        //backpoint add
        void hook_add(HWord addr, Hook_CallBack cb, TRControlFlags cflag);
        void hook_add(HWord addr, Hook_CallBack cb) { hook_add(addr, cb, CF_None); };
        bool get_hook(Hook_struct& hs, HWord addr);

    public:

        vex_context(Int max_threads);
        
        void constructer();
        virtual ~vex_context();
        void hook_del(HWord addr);
        void hook_read(Hook_Read read_call) { m_hook_read = (void*)read_call; }
        void hook_write(Hook_Write write_call) { m_hook_write = (void*)write_call; }
        Hook_Read get_hook_read() { return (Hook_Read)m_hook_read; }
        Hook_Write get_hook_write() { return (Hook_Write)m_hook_write; }
        IRSBCache* get_irsb_cache() { return m_irsb_cache; }
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
        void idx2Value_Decl_add(HWord addr, Hook_idx2Value _func) { m_tableIdxDict[addr] = _func; };
        void idx2Value_Decl_del(HWord addr) { m_tableIdxDict.erase(m_tableIdxDict.find(addr)); };
        bool idx2Value_base_exist(HWord base) { return m_tableIdxDict.find(base) != m_tableIdxDict.end(); }
        z3::expr idx2value(TR::StateBase& state, HWord base, Z3_ast index);

    };


};






#endif
