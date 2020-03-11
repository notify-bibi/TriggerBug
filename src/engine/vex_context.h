#pragma once
#ifndef _VEX_CONTEXT_
#define  _VEX_CONTEXT_
#include "thread_pool/thread_pool.h"
#include "engine/engine.h"

UInt gMaxThreadsNum();

namespace TR {

    class vex_info;
    class vctx_base;
    template<typename _> class vex_context;

    typedef State_Tag(*Hook_CB)(void*/*obj*/);
    //�õ���ast����Z3_inc_ref
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
        UInt m_IRoffset_IP;

        vex_info(VexArch guest, const char* filename);
    public:
        static void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk, VexArch guest, ULong traceflags);
        void init_vta_chunk(VexTranslateArgs& vta_chunk, VexGuestExtents& vge_chunk) { init_vta_chunk(vta_chunk, vge_chunk, m_guest, m_traceflags); }
        inline ULong getFlags() const { return m_traceflags; }
        IRConst const* softwareBptConst() const { return &m_bpt_code; };
        void softwareBptStore(UChar* dst) { memcpy(dst, &m_bpt_code.Ico.U8, IRConstTag2nb(m_bpt_code.tag)); };
        //���뱣��һ��virtual
        virtual UInt bit_wide() { VPANIC("??"); }
        static UInt gMaxThreadsNum();
        static IRConst gsoftwareBpt(VexArch guest);
        static UInt gRegsIpOffset(VexArch guest);
        inline const char* gbin() const { return m_bin; }
        VexRegisterUpdates gRegisterUpdates() const { return m_iropt_register_updates_default; };
        inline VexArch gguest()const { return m_guest; }
        inline Int giropt_level() const { return m_iropt_level; }
        inline UInt gmax_insns() const { return m_guest_max_insns; }
        inline GuestSystem gguest_system() const { return m_guest_system; }
        inline UInt gmax_threads_num() const { return m_maxThreadsNum; }
        inline ULong gtraceflags() const { return m_traceflags; }
        inline UInt gRegsIpOffset() const { return m_IRoffset_IP; }

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
        //ģ������ϵ� software backpoint callback
        std::hash_map<Addr64, Hook_struct> m_callBackDict;
        std::hash_map<Addr64/*static table base*/, TableIdx_CB> m_tableIdxDict;

        vex_context(vex_context const&) = delete;
        void operator = (vex_context const&) = delete;
        void set_top_state(State<ADDR>* s) { vassert(!m_top_state); m_top_state = s; }
    public:
        vex_context(VexArch guest, const char* filename) :vctx_base(guest, filename), m_top_state(nullptr) {};
        //backpoint add
        void hook_add(ADDR addr, State_Tag(*_func)(State<ADDR>*), TRControlFlags cflag);

        bool get_hook(Hook_struct& hs, ADDR addr);

        void hook_del(ADDR addr);

        inline ThreadPool& pool() { return m_pool; };


        /*read static_table from symbolic address  ���� index �� �ó������� ֮��Ĺ�ϵ ��Ȼֻ����һ���� ��DES��4����̬��
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
        void idx2Value_Decl_add(Addr64 addr, Z3_ast(*_func) (State<ADDR>*, Addr64 /*base*/, Z3_ast /*idx*/)) { m_tableIdxDict[addr] = (TableIdx_CB)_func; };
        void idx2Value_Decl_del(Addr64 addr) { m_tableIdxDict.erase(m_tableIdxDict.find(addr)); };

        UInt bit_wide() override { return (UInt)((sizeof(ADDR))<<3); }
    };

    using ctx32 = vex_context<Addr32>;
    using ctx64 = vex_context<Addr64>;

};






#endif