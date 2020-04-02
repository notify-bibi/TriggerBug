#pragma once
#ifndef _ADDRESSING_MODE_
#define _ADDRESSING_MODE_

#include <deque>
#include "api/c++/z3++.h"
#include "engine/variable.h"
#include "libvex_basictypes.h";

#define BIT_BLAST_MAX_BIT 14

namespace TR {
    template<typename ADDR>
    class addressingMode
    {
    public:
        enum addressingModeKind {
            cant_analysis = 0,
            found_base_and_offset,
            support_bit_blast
        };

    private:
        struct sbit_struct {
            Z3_ast sym_ast;
            bool rbit;
            UInt idx;
        };

        struct sbit_struct_r {
            sbit_struct sbit;
            ADDR sign_mask;
            UInt nbit;
        };

        //超集的解遍历算法
    public:
        class iterator
        {
            struct shift_mask {
                UChar shift;
                ADDR mask;
            };

        private:
            ADDR m_sym_mask;
            ADDR m_or_mask;
            ADDR tmp_bit_blast;
            ADDR tmp_target_bit_blast;
            struct shift_mask m_sym_ml[BIT_BLAST_MAX_BIT];
            UInt m_sym_ml_n;


            struct shift_mask m_sign_ml[32];
            UInt m_sign_ml_n;

        public:

            iterator(addressingMode<ADDR>& am);


            inline bool check() const
            {
                return tmp_bit_blast != tmp_target_bit_blast;
            }

            inline void next()
            {
                tmp_bit_blast++;
            }

            inline ADDR operator*()
            {
                ADDR re = 0;
                for (UInt sign_ml_n = 0; sign_ml_n < m_sign_ml_n; sign_ml_n++) {
                    if ((tmp_bit_blast >> m_sign_ml[sign_ml_n].shift) & 1) {
                        re |= m_sign_ml[sign_ml_n].mask;
                    }
                }
                for (UInt sym_ml_n = 0; sym_ml_n < m_sym_ml_n; sym_ml_n++) {
                    re |= (tmp_bit_blast << m_sym_ml[sym_ml_n].shift) & m_sym_ml[sym_ml_n].mask;
                }
                return re | m_or_mask;
            }
        };



    private:
        z3::context& m_ctx;
        z3::expr m_symbolic;
        z3::expr m_offset;
        ADDR m_base;
        std::deque<ADDR> m_sign_mask;
        ADDR m_sym_mask;
        UInt m_sym_mask_n;
        ADDR m_or_mask;

        addressingModeKind m_analysis_kind;
    public:
        addressingMode(const z3::expr& e);

        inline addressingMode(const addressingMode<ADDR>& a) :
            m_ctx(a.m_ctx),
            m_offset(a.m_offset),
            m_base(a.m_base),
            m_symbolic(a.m_symbolic)
        { }

        void offset2opAdd(std::deque<z3::expr>& ret) {  _offset2opAdd(ret, m_offset); }

    private:
        // ast(symbolic address) = numreal(base) + symbolic(offset) 
        bool ast2baseAoffset();

        //分析offset 使分析器能够求解出超集
        bool offset_bit_blast();

    public:
        addressingModeKind analysis_kind() {
            return m_analysis_kind;
        }

        inline ADDR getBase() {
            assert(m_analysis_kind != cant_analysis);
            return m_base;
        }

        inline z3::expr getoffset() {
            assert(m_analysis_kind != cant_analysis);
            return m_offset;
        }


        inline void operator=(const addressingMode<ADDR>& a)
        {
            this->~addressingMode();
            this->addressingMode<ADDR>::addressingMode(a);
        }

        inline ~addressingMode() {
        }


        inline iterator begin() {
            assert(m_analysis_kind == support_bit_blast);
            return iterator(*this);
        }

        void print();

        void print_offset() {
            std::cout << m_offset << std::endl;
        }
    private:
        static z3::expr _ast2base(z3::expr& base,
            z3::expr const& e,
            UInt deep, UInt max_deep
        );

        static sbit_struct _check_is_extract(z3::expr const& e, UInt idx);
        //a=b+c+d+e...+z -> b c d e
        static void _offset2opAdd(std::deque<z3::expr>& ret, z3::expr const& e);
        static bool _check_add_no_overflow(z3::expr const& e1, z3::expr const& e2);
    };




};



#endif