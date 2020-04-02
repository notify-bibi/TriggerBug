#pragma once
#ifndef _MEM_MAP_
#define _MEM_MAP_
#include "engine/engine.h"



namespace TR {

    template<class ST>
    class mapping {
    public:
        typedef struct PAGE_link {
            UShort index;
            PAGE_link* prev;
            PAGE_link* next;
        }PAGE_link;

        typedef struct PT {
            UShort used;
            UShort index;
            PAGE_link* top;
            PT* prev;
            PT* next;
            UInt size;
            ST** pt;
        }PT;

        typedef struct PDT {
            UShort used;
            UShort index;
            PT* top;
            PDT* prev;
            PDT* next;
            UInt size;
            PT** pt;
        }PDT;

        typedef struct PDPT {
            UShort used;
            UShort index;
            PDT* top;
            PDPT* prev;
            PDPT* next;
            UInt size;
            PDT** pt;
        }PDPT;

        typedef struct PML4T {
            UShort used;
            PDPT* top;
            UInt size;
            PDPT** pt;
        }PML4T;

    private:
        PML4T _CR3_;

        virtual ST* map_interface(ULong address) { vassert(0); };
        virtual void copy_interface(ST* pt_dst[1], ST* pt_src[1]) { vassert(0); };
        virtual void unmap_interface(ST* pt[1]) { vassert(0); };
        
    public:
        PML4T* CR3[1];
        mapping() {
            CR3[0] = &_CR3_;
            memset(&_CR3_, 0, sizeof(PML4T));
        }

        //客户机的分配空间算法 类似cpu的硬件虚拟映射技术。这里我们使用软件虚拟映射
        ULong map(ULong address, ULong length);

        //类似于linux的sys_fork.写时复制.速度快
        void copy(PML4T* cr3);

        //释放物理页
        ULong unmap(ULong address, ULong length);
        
        void recycle();

        ~mapping() { vassert(!CR3[0]); }

        //虚拟映射一个虚拟地址
        inline ST** get_pointer_of_mem_page(Addr64 address) {
            UShort PML4T_ind = (address >> 39 & 0x1ff);
            UShort PDPT_ind = (address >> 30 & 0x1ff);
            UShort PDT_ind = (address >> 21 & 0x1ff);
            UShort PT_ind = (address >> 12 & 0x1ff);
            if (PML4T_ind < (*CR3)->size) {
                PDPT* pdpt = (*CR3)->pt[PML4T_ind];
                if (pdpt && PDPT_ind < pdpt->size) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    if (pdt && PDT_ind < pdt->size) {
                        PT* pt = pdt->pt[PDT_ind];
                        if (pt && PT_ind < pt->size) {
                            return &pt->pt[PT_ind];
                        }
                    }
                }
            }
            return nullptr;
        };

        inline ST** get_pointer_of_mem_page(Addr32 address) {
            UShort PDPT_ind = (address >> 30 & 0x3);
            UShort PDT_ind = (address >> 21 & 0x1ff);
            UShort PT_ind = (address >> 12 & 0x1ff);
            if ((*CR3)->size) {
                PDPT* pdpt = (*CR3)->pt[0];
                if (pdpt && PDPT_ind < pdpt->size) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    if (pdt && PDT_ind < pdt->size) {
                        PT* pt = pdt->pt[PDT_ind];
                        if (pt && PT_ind < pt->size) {
                            return &pt->pt[PT_ind];
                        }
                    }
                }
            }
            return nullptr;
        };

        inline ST* get_mem_page(Addr32 address) {
            ST** r = get_pointer_of_mem_page(address);
            return (r) ? r[0] : nullptr;
        }

        inline ST* get_mem_page(Addr64 address) {
            ST** r = get_pointer_of_mem_page(address);
            return (r) ? r[0] : nullptr;
        }

        //find block reverse;
        inline ST** find_mem_page_reverse(Addr64 address, Addr64 &ret) {
            Int PML4T_ind = (address >> 39 & 0x1ff);
            Int PDPT_ind = (address >> 30 & 0x1ff);
            Int PDT_ind = (address >> 21 & 0x1ff);
            Int PT_ind = (address >> 12 & 0x1ff);
            for (; PML4T_ind >= 0; PML4T_ind--) {
                PDPT* pdpt = (*CR3)->pt[PML4T_ind];
                for (; pdpt && PDPT_ind >= 0; PDPT_ind--) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    for (; pdt && PDT_ind >= 0; PDT_ind--) {
                        PT* pt = pdt->pt[PDT_ind];
                        for (; pt && PT_ind >= 0; PT_ind--) {
                            if (pt->pt[PT_ind]) {
                                ret = (((Addr64)PML4T_ind) << 39) | (((Addr64)PDPT_ind) << 30) | (((Addr64)PDT_ind) << 21) | (((Addr64)PT_ind) << 12);
                                return &pt->pt[PT_ind];
                            }
                        }
                    }
                }
            }
            return nullptr;
        };

        //find block reverse;
        inline ST** find_mem_page_reverse(Addr32 address, Addr32& ret) {
            Int PDPT_ind = (address >> 30 & 0x1ff);
            Int PDT_ind = (address >> 21 & 0x1ff);
            Int PT_ind = (address >> 12 & 0x1ff);
            if ((*CR3)->size) {
                PDPT* pdpt = (*CR3)->pt[0];
                for (; pdpt && PDPT_ind >= 0; PDPT_ind--) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    for (; pdt && PDT_ind >= 0; PDT_ind--) {
                        PT* pt = pdt->pt[PDT_ind];
                        for (; pt && PT_ind >= 0; PT_ind--) {
                            if (pt->pt[PT_ind]) {
                                ret = (((Addr32)PDPT_ind) << 30) | (((Addr32)PDT_ind) << 21) | (((Addr32)PT_ind) << 12);
                                return &pt->pt[PT_ind];
                            }
                        }
                    }
                }
            }
            return nullptr;
        };


        //find block forward;
        inline ST** find_mem_page_forward(Addr32 address, Addr32& ret) {
            UInt PDPT_ind = (address >> 30 & 0x1ff);
            UInt PDT_ind = (address >> 21 & 0x1ff);
            UInt PT_ind = (address >> 12 & 0x1ff);
            if((*CR3)->size) {
                PDPT* pdpt = (*CR3)->pt[0];
                for (; pdpt && PDPT_ind < pdpt->size; PDPT_ind++) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    for (; pdt && PDT_ind < pdt->size; PDT_ind++) {
                        PT* pt = pdt->pt[PDT_ind];
                        for (; pt && PT_ind < pt->size; PT_ind++) {
                            if (pt->pt[PT_ind]) {
                                ret = (((Addr32)PDPT_ind) << 30) | (((Addr32)PDT_ind) << 21) | (((Addr32)PT_ind) << 12);
                                return &pt->pt[PT_ind];
                            }
                        }
                    }
                }
            }
            return nullptr;
        };

        inline ST** find_mem_page_forward(Addr64 address, Addr64& ret) {
            UInt PML4T_ind = (address >> 39 & 0x1ff);
            UInt PDPT_ind = (address >> 30 & 0x1ff);
            UInt PDT_ind = (address >> 21 & 0x1ff);
            UInt PT_ind = (address >> 12 & 0x1ff);
            for (; PML4T_ind < (*CR3)->size; PML4T_ind++) {
                PDPT* pdpt = (*CR3)->pt[PML4T_ind];
                for (; pdpt && PDPT_ind < pdpt->size; PDPT_ind++) {
                    PDT* pdt = pdpt->pt[PDPT_ind];
                    for (; pdt && PDT_ind < pdt->size; PDT_ind++) {
                        PT* pt = pdt->pt[PDT_ind];
                        for (; pt && PT_ind < pt->size; PT_ind++) {
                            if (pt->pt[PT_ind]) {
                                ret = (((Addr64)PML4T_ind) << 39) | (((Addr64)PDPT_ind) << 30) | (((Addr64)PDT_ind) << 21) | (((Addr64)PT_ind) << 12);
                                return &pt->pt[PT_ind];
                            }
                        }
                    }
                }
            }
            return nullptr;
        };
    };

};





#endif