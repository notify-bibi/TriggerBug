/*clang-cl.exe -E MKG.c 1>> xx.txt*/
extern "C" {
#include "libvex.h"
#include "main_util.h"
}
#include <deque>
extern std::deque<void*> LibVEX_Alloc_transfer(void);

#define GEN_MKG 

#define MKG_AMD64
#define MKG_X86
#define MKG_ARM
#define MKG_ARM64
#define MKG_MIPS
#define MKG_NANOMIPS
#define MKG_PPC

#define MKG_VAR_CALL(NAME_SPACE, TYPE, VAR) TYPE (*NAME_SPACE##_##VAR##_var_call());    

extern "C" {
#include "config.h"
}

#undef MKG_VAR_CALL
#define MKG_VAR_CALL(NAME_SPACE, TYPE, VAR)             \
TYPE* NAME_SPACE##_##VAR##_var_call(){ static thread_local TYPE VAR; return &VAR; }                  \



extern "C" {
#include "config.h"
#include <corecrt_malloc.h>
}

#undef MKG_VAR_CALL

#include "gen_global_var_call.hpp"

static_assert(sizeof(IRExpr) == 32, "gggg");
//static constexpr int sizeofARMInstr = sizeof(ARMInstr);
//static_assert(sizeofARMInstr <= 28, "gggg");



typedef struct {
    void* instance;
    const UChar* (*guest_insn_control_method)(void* instance, Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code);
}guest_insn_control_type;


static thread_local guest_insn_control_type guest_insn_control = { nullptr, nullptr };

void bb_insn_control_obj_set(void* instance, const UChar* (*guest_insn_control_method)(void*, Addr, Long, const UChar*)) {
    guest_insn_control = { instance,  guest_insn_control_method };
}

const UChar* /*out guest_code*/ guest_generic_bb_insn_control(Addr guest_IP_sbstart, Long delta, const UChar* /*in guest_code*/ guest_code) {
    guest_insn_control_type* local_guest_insn_control = &guest_insn_control;
    const UChar* new_guest_code = local_guest_insn_control->guest_insn_control_method(local_guest_insn_control->instance, guest_IP_sbstart, delta, guest_code);
    return new_guest_code;
}



// valgrind mem Alloc

class __attribute__((aligned(16)))  LibVEX_Alloc_M {
   static const int one_chunk_size = 0x400;
   int m_curr_chunk_size = one_chunk_size;

    HChar*  temporary ;
    HChar* private_LibVEX_alloc_first;
    HChar* private_LibVEX_alloc_curr;
    HChar* private_LibVEX_alloc_last;
    std::deque<void*> m_alloc_list;
    VexAllocMode mode;

public:
    inline LibVEX_Alloc_M() :temporary(nullptr), private_LibVEX_alloc_first(nullptr), private_LibVEX_alloc_curr(nullptr), private_LibVEX_alloc_last(nullptr){
        this->m_alloc_list.clear();
        this->private_LibVEX_alloc_OOM();
    }

    inline void* LibVEX_Alloc_inline(SizeT nbytes) {

        struct align {
            char c;
            union {
                char c;
                short s;
                int i;
                long l;
                long long ll;
                float f;
                double d;
                /* long double is currently not used and would increase alignment
                   unnecessarily. */
                   /* long double ld; */
                void* pto;
                void (*ptf)(void);
            } x;
        };

        /* Make sure the compiler does no surprise us */
        vassert(offsetof(struct align, x) <= REQ_ALIGN);

#if 0
        if (0x800 == nbytes) {
            printf("??");
        }
        temporary = (HChar*)malloc(nbytes);
        m_alloc_list.push_back(temporary);
        memset(temporary, 0x23, nbytes);
        /* Nasty debugging hack, do not use. */
        return temporary;
#else
        HChar* curr;
        HChar* next;
        SizeT  ALIGN;
        ALIGN = offsetof(struct align, x) - 1;
        curr = private_LibVEX_alloc_curr;
        next = curr + ((nbytes + ALIGN) & ~ALIGN);
        INNER_REQUEST(next += 2 * VEX_REDZONE_SIZEB);
        if (UNLIKELY(next >= private_LibVEX_alloc_last)) {
            private_LibVEX_alloc_OOM();
            return LibVEX_Alloc_inline(nbytes);
        }
        private_LibVEX_alloc_curr = next;
        INNER_REQUEST(curr += VEX_REDZONE_SIZEB);
        INNER_REQUEST(VALGRIND_MEMPOOL_ALLOC(private_LibVEX_alloc_first,
            curr, nbytes));
        vassert(curr + nbytes < private_LibVEX_alloc_last);
        //memset(curr, 0x24, nbytes);
        return curr;
#endif
    
    }



    inline void vexSetAllocMode(VexAllocMode mode) {
        this->mode = mode;
    }

    inline VexAllocMode vexGetAllocMode(void) {
        return this->mode;
    }


    inline void  vexAllocSanityCheck(void) {

    }


    inline void  vexSetAllocModeTEMP_and_clear(void) {

    }


    void  private_LibVEX_alloc_OOM(void)  {
        if (UNLIKELY(temporary && private_LibVEX_alloc_curr == private_LibVEX_alloc_first)) {
            free(m_alloc_list.back());
            m_alloc_list.pop_back();
            m_curr_chunk_size += one_chunk_size;
        }
        temporary = (HChar*)malloc(m_curr_chunk_size);
        //memset(temporary, 0x11, m_curr_chunk_size);
        private_LibVEX_alloc_first = temporary;
        private_LibVEX_alloc_curr = temporary;
        private_LibVEX_alloc_last = &temporary[m_curr_chunk_size];
        m_alloc_list.push_back(temporary);
    }
    
    std::deque<void*> transfer() {
        //life_cycle_transfer = true;
        std::deque<void*> res = m_alloc_list;
        m_alloc_list.clear();
        this->~LibVEX_Alloc_M();
        new (this) LibVEX_Alloc_M;
        return res;
    }
    
    inline ~LibVEX_Alloc_M() {
        /*if (life_cycle_transfer) { 
            vassert(m_alloc_list.empty());
            return;
        }*/
        for (auto alloc_tmp : m_alloc_list) {
            free(alloc_tmp);
        }
    }
};



static thread_local LibVEX_Alloc_M gLibVEX_Alloc_M;



void* LibVEX_Alloc_inline(SizeT nbytes)
{
    return gLibVEX_Alloc_M.LibVEX_Alloc_inline(nbytes);
}

void         vexSetAllocMode(VexAllocMode mode) {
    gLibVEX_Alloc_M.vexSetAllocMode(mode);
}

VexAllocMode vexGetAllocMode(void) {
    return gLibVEX_Alloc_M.vexGetAllocMode();
}

void         vexAllocSanityCheck(void) {
    gLibVEX_Alloc_M.vexAllocSanityCheck();
}

void vexSetAllocModeTEMP_and_clear(void) {
    gLibVEX_Alloc_M.vexSetAllocModeTEMP_and_clear();
}

std::deque<void*> LibVEX_IRSB_transfer(void) {
    return gLibVEX_Alloc_M.transfer();
}
