#pragma once
#ifndef _ENV_VEX_
#define _ENV_VEX_

#include "instopt/engine/engine.h"
#include "instopt/engine/vex_context.h"
#include <map>
#include "instopt/engine/irsb_cache.h"

namespace TR {
    class MBase;

    template<class T, std::size_t N>
    class static_vector
    {
        // properly aligned uninitialized storage for N T's
        typename std::aligned_storage<sizeof(T), alignof(T)>::type data[N];
        std::size_t m_size = 0;

    public:
        // Create an object in aligned storage
        template<typename ...Args> void emplace_back(Args&&... args)
        {
            if (m_size >= N) // possible error handling
                throw std::bad_alloc{};

            // construct value in memory of aligned storage
            // using inplace operator new
            new(&data[m_size]) T(std::forward<Args>(args)...);
            ++m_size;
        }

        // Access an object in aligned storage
        T& operator[](std::size_t pos)
        {
            // note: needs std::launder as of C++17
            return *reinterpret_cast<T*>(&data[pos]);
        }

        inline std::size_t size() { return m_size; }

        // Delete objects from aligned storage
        ~static_vector()
        {
            for (std::size_t pos = 0; pos < m_size; ++pos) {
                // note: needs std::launder as of C++17
                reinterpret_cast<T*>(&data[pos])->~T();
            }
        }
    };


    template<std::size_t N>
    class ir_temp_vector : public static_vector<sv::tval, N> {
        Z3_context m_ctx;
    public:
        ir_temp_vector(Z3_context ctx) :m_ctx(ctx) {
            for (std::size_t pos = 0; pos < N; ++pos) {
                static_vector::emplace_back(sv::tval());
            }
        }
    };


    class IR_Manager {
        friend class EmuEnvironment;
        friend class EmuEnvGuest;
        friend class EmuEnvHost;

        using tval_thunk = ir_temp_vector<MAX_IRTEMP>;
        Z3_context m_ctx;
        std::vector<tval_thunk*> m_ir_unit;
        UInt   m_size_ir_temp;
        void clear();
        IR_Manager() {};
        IR_Manager(Z3_context ctx);
        sv::tval& operator[](UInt idx);
        ~IR_Manager();
    };



    // __declspec(align(32))
     
    class EmuEnvironment {
        friend class EmuEnvGuest;
        friend class EmuEnvHost;

        VexTranslateArgs    m_vta_chunk;
        VexGuestExtents     m_vge_chunk;

        VexRegisterUpdates m_pxControl;
        VexTranslateResult m_res;

        Addr64 m_guest_start_of_block = 0;
        UInt m_base_block_sz = 0;
        bool   m_is_dynamic_block = false;//Need to refresh IRSB memory?
        bool   m_is_dirty_mode = false;   // is dirty call mode

        EmuEnvironment(VexArch arch, ULong traceflags) {
            set_vta_chunk(arch, traceflags);
        }
    public:
        void set_vta_chunk(VexArch arch, ULong traceflags);
        inline void set_dirty_mode() { m_is_dirty_mode = true; }
        inline void clean_dirty_mode() { m_is_dirty_mode = false; }
        inline VexTranslateArgs* get_ir_vex_translate_args() { return &m_vta_chunk; }
        inline VexGuestExtents* get_ir_vex_guest_extents() { return &m_vge_chunk; }
        inline VexRegisterUpdates* get_pxControl() { return &m_pxControl; }
        inline VexTranslateResult* get_res(){ return &m_res; }

        inline bool check() { return m_is_dynamic_block; };
        //emu process write method will call back
        virtual void block_integrity(Addr ea, UInt sz);

        virtual void set_guest_bb_insn_control_obj() {};
        //new ir temp
        virtual void malloc_ir_buff(Z3_context ctx) {};
        //free ir temp
        virtual void free_ir_buff() {};
        // translate
        virtual irsb_chunk translate_front(HWord /*dirty/guest_addr*/) { return irsb_chunk{}; };
        virtual sv::tval& operator[](UInt idx) = nullptr ;

        // 模拟前调用
        void set_guest_bytes_addr(const UChar* bytes, Addr64 virtual_addr);
        void set_host_addr(Addr64 host_virtual_addr);

        virtual ~EmuEnvironment();
    };

    class EmuEnvGuest : public EmuEnvironment {
        vex_context& m_vctx;
        IR_Manager m_ir_temp;
        MBase& m_mem;
    public:
        //init vex
        EmuEnvGuest(vex_context& vctx, vex_info const& info, MBase& mem_obj);

        void block_integrity(Addr ea, UInt sz) override;
        void set_guest_bb_insn_control_obj() override;

        //void block_integrity(Addr address, UInt insn_block_delta) override;

        inline bool check() { return m_is_dynamic_block; };
        //new ir temp
        virtual void malloc_ir_buff(Z3_context ctx) override;
        //free ir temp
        virtual void free_ir_buff() override;
        // guest translate
        irsb_chunk translate_front( HWord /*guest_addr*/) override;
        virtual sv::tval& operator[](UInt idx) override;
    };


};


#endif  //! _ENV_VEX_;