#pragma once
#ifndef _ENV_VEX_
#define _ENV_VEX_

#include "engine/engine.h"
#include "engine/vex_context.h"
#include <map>   

namespace TR {

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
    class ir_temp_vector : public static_vector<tval, N> {
        Z3_context m_ctx;
    public:
        ir_temp_vector(Z3_context ctx) :m_ctx(ctx) {
            for (std::size_t pos = 0; pos < N; ++pos) {
                static_vector::emplace_back(tval());
            }
        }
    };


    class IR_Manager {
        friend class EmuEnvironment;
        using tval_thunk = ir_temp_vector<MAX_IRTEMP>;
        Z3_context m_ctx;
        std::vector<tval_thunk*> m_ir_unit;
        UInt   m_size_ir_temp;
        void clear();
        IR_Manager(Z3_context ctx);
        tval& operator[](UInt idx);
        ~IR_Manager();
    };



    __declspec(align(32))
    class EmuEnvironment {
        Addr64 m_guest_start_of_block = 0;
        bool   m_is_dynamic_block = false;//Need to refresh IRSB memory?
        VexTranslateArgs    m_vta_chunk;
        VexGuestExtents     m_vge_chunk;
        vex_info&           m_info;
        std::map<Addr, UInt> m_cache_map;/*block address -> size*/
        IR_Manager          m_ir_temp;
    public:
        //init vex
        template<typename THword>
        EmuEnvironment(vex_info const& info, MEM<THword>& mem_obj, VexArch host);
        /*
        template<>
        EmuEnvironment(vex_info const& info, MEM<Addr32>& mem_obj, VexArch host);
        template<>
        EmuEnvironment(vex_info const& info, MEM<Addr64>& mem_obj, VexArch host);*/

        //new ir temp
        void malloc_ir_buff(Z3_context ctx);
        //free ir temp
        void free_ir_buff();
        // translate
        template<typename THword>
        IRSB* translate_front(MEM<THword>& mem, Addr guest_addr);
        //set guest_start_of_block to check block changed by guest
        void set_start(Addr64 s);

        void set_guest_bytes_addr(const UChar* bytes, Addr64 virtual_addr);

        /*template<typename THword>
        void set_guest_code_temp(MEM<THword>& mem_obj, Addr64 virtual_addr, Hook_struct const& hs);*/

        

        inline void set_host_addr(Addr64 host_virtual_addr) {
            m_vta_chunk.guest_bytes = (UChar*)(host_virtual_addr);
            m_vta_chunk.guest_bytes_addr = host_virtual_addr;
        }

        /*inline static_vector<tval, MAX_TMP>& ir_tmp() {
            return *m_ir_temp_trunk;
        }*/

        tval& operator[](UInt idx) { return  m_ir_temp[idx]; }

        inline VexTranslateArgs* get_ir_vex_translate_args() { return &m_vta_chunk; }
        inline VexGuestExtents* get_ir_vex_guest_extents() { return &m_vge_chunk; }
        //emu process write method will call back
        void block_integrity(bool is_code, Addr address, UInt insn_block_delta);

        inline bool check() { return m_is_dynamic_block; };

        ~EmuEnvironment();
    };


};


#endif  //! _ENV_VEX_;