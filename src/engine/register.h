#pragma once
/*++
Copyright (c) 2019 Microsoft Corporation
Module Name:
    Reister.class: 
Abstract:
    API list;
Author:
    WXC 2019-05-31.
Revision History:
--*/
#ifndef REGISTER_HL_CD
#define REGISTER_HL_CD

#include "engine/engine.h"
#include "engine/variable.h"
#include "engine/basic_var.hpp"
#include <Windows.h>


#define fastMaskB(n) fastMask(((n)<<3))
#define fastMaskBI1(n) fastMask((((n)+1)<<3))

namespace TR {

#ifdef USE_HASH_AST_MANAGER
    class AstManager {
        friend class AstManagerX;
        template <int maxlength>
        friend class Register;
    public:
        std::hash_map<Int, Z3_ast> m_mem;
        class AstManagerX {
            std::hash_map<Int, Z3_ast>& m_mem;
            Int m_offset;
        public:
            inline AstManagerX(AstManager& am) :m_mem(am.m_mem), m_offset(0) {}
            inline AstManagerX(AstManager& am, Int offset) : m_mem(am.m_mem), m_offset(offset) {}
            inline AstManagerX(std::hash_map<Int, Z3_ast>& mem, Int offset) : m_mem(mem), m_offset(offset) {}
            inline Z3_ast& operator[](Int idx) { return m_mem[m_offset + idx]; }
            AstManagerX operator+(Int offset) { return AstManagerX(m_mem, m_offset + offset); }
            AstManagerX operator-(Int offset) { return AstManagerX(m_mem, m_offset - offset); }
        };
        inline AstManager() {}
        inline Z3_ast& operator[](Int idx) { return m_mem[idx]; }
        inline AstManagerX operator+(Int offset) { return AstManagerX(*this, offset); }
        inline AstManagerX operator-(Int offset) { return AstManagerX(*this, -offset); }
    };


#endif

#ifdef USE_HASH_AST_MANAGER
    extern Z3_ast Reg2Ast(int nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX& m_ast, z3::vcontext& ctx);
    extern Z3_ast Reg2AstSSE(int nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX& m_ast, z3::vcontext& ctx);
#else
    extern Z3_ast Reg2Ast(int nbytes, UChar* m_bytes, UChar* m_fastindex, Z3_ast* m_ast, Z3_context ctx);
    extern Z3_ast Reg2AstSSE(int nbytes, UChar* m_bytes, UChar* m_fastindex, Z3_ast* m_ast, Z3_context ctx);
#endif

#ifdef USE_HASH_AST_MANAGER
    extern Z3_ast Reg2Ast(int nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX& m_ast, z3::vcontext& ctx, z3::vcontext& toctx);
    extern Z3_ast Reg2AstSSE(int nbytes, UChar* m_bytes, UChar* m_fastindex, AstManager::AstManagerX& m_ast, z3::vcontext& ctx, z3::vcontext& toctx);
#else
    extern Z3_ast Reg2Ast(int nbytes, UChar* m_bytes, UChar* m_fastindex, Z3_ast* m_ast, Z3_context ctx, Z3_context toctx);
    extern Z3_ast Reg2AstSSE(int nbytes, UChar* m_bytes, UChar* m_fastindex, Z3_ast* m_ast, Z3_context ctx, Z3_context toctx);
#endif




#define sse_check_zero_X256(data)  (_mm256_movemask_epi8(_mm256_cmpeq_epi64(_mm256_setzero_si256(), _mm256_loadu_si256((__m256i*)(data)))) != -1)
#define sse_check_zero_X128(data)  (_mm_movemask_epi8(_mm_cmpeq_epi64(_mm_setzero_si128(), _mm_loadu_si128((__m128i*)(data)))) != -1)


    //Symbolic

    //class RegUnit {
    //private:
    //    struct _Mstruct {
    //        unsigned long long m_ast : 48;
    //        bool w : 1;
    //        bool r : 1;
    //        bool e : 1;
    //        bool hook : 1;
    //    } pack;
    //public:
    //    inline void operator =(Z3_ast _ast) {
    //        pack.m_ast = (unsigned long long)_ast;
    //    }
    //    inline operator Z3_ast() {
    //        return (Z3_ast)pack.m_ast;
    //    }
    //    inline bool ar() {
    //        return pack.r;
    //    }
    //    inline bool aw() {
    //        return pack.w;
    //    }
    //    inline bool ae() {
    //        return pack.e;
    //    }
    //};


    template<int maxlength>
    class Symbolic
    {
        template <int maxlength>
        friend class Register;
    public:
        z3::vcontext& m_ctx;
#ifdef USE_HASH_AST_MANAGER
        AstManager m_ast;
#else
        __declspec(align(8)) Z3_ast *m_ast;
#endif
        /* SETFAST macro Setfast overstepping the bounds is not thread-safe(heap), so +32 solves the hidden bug !*/
        __declspec(align(32)) unsigned char m_fastindex[maxlength + 32];



        inline Symbolic(z3::vcontext& ctx) : m_ctx(ctx) {
            memset(m_fastindex, 0, sizeof(m_fastindex));
#ifndef USE_HASH_AST_MANAGER
            m_ast = new Z3_ast[maxlength];
#endif
        }
        inline Symbolic(z3::vcontext& ctx, Symbolic<maxlength>* father) : m_ctx(ctx) {
            memcpy(m_fastindex, father->m_fastindex, maxlength);
            memset(m_fastindex + maxlength, 0, 32);
#ifndef USE_HASH_AST_MANAGER
            Int _pcur = maxlength - 1;
            DWORD N;
            for (; _pcur > 0; ) {
                if (_BitScanReverse64(&N, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1[_pcur % 8])) {
                    _pcur = ALIGN(_pcur, 8) + (N >> 3);
                    _pcur = _pcur - m_fastindex[_pcur] + 1;
                    m_ast[_pcur] = Z3_translate(father->m_ctx, father->m_ast[_pcur], m_ctx);
                    vassert(m_ast[_pcur] != NULL);
                    Z3_inc_ref(m_ctx, m_ast[_pcur]);
                    _pcur--;
                }
                else {
                    _pcur = ALIGN(_pcur - 8, 8) + 7;
                }
            };
#else
            std::hash_map<Int, Z3_ast>& fast = father->m_ast.m_mem;
            auto it_end = fast.end();
            for (auto it = fast.begin(); it != it_end; it++) {
                if (m_fastindex[it->first] == 1) {
                    Z3_ast translate_ast = Z3_translate(father->m_ctx, it->second, m_ctx);
                    m_ast[it->first] = translate_ast;
                    vassert(translate_ast != NULL);
                    Z3_inc_ref(m_ctx, translate_ast);
                }
            }
#endif
        }
        inline ~Symbolic<maxlength>() {
            int _pcur = maxlength - 1;
            DWORD N;
            for (; _pcur > 0; ) {
                if (_BitScanReverse64(&N, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1(_pcur % 8))) {
                    _pcur = ALIGN(_pcur, 8) + (N >> 3);
                    _pcur = _pcur - m_fastindex[_pcur] + 1;
                    Z3_dec_ref(m_ctx, m_ast[_pcur]);
                    _pcur--;
                }
                else {
                    _pcur = ALIGN(_pcur - 8, 8) + 7;
                }
            };
#ifndef USE_HASH_AST_MANAGER
            delete m_ast;
#endif
        }
    };


    //Record
    //写入记录器，8字节记录为m_flag的一个bit
    template<int maxlength>
    class Record {
    public:
        UChar m_flag[(maxlength >> 6) + 1];
        Record() {
            memset(m_flag, 0, sizeof(m_flag));
            UInt shift = (maxlength & ((1 << 6) - 1)) >> 3;
            m_flag[maxlength >> 6] = shift ? 0x1 << shift : 0x1;
        };

        void clearRecord() {
            memset(m_flag, 0, sizeof(m_flag));
            UInt shift = (maxlength & ((1 << 6) - 1)) >> 3;
            m_flag[maxlength >> 6] = shift ? 0x1 << shift : 0x1;
        };

        template<int nbytes>
        inline void write(int offset) {
            *(UShort*)(m_flag + (offset >> 6)) |=
                (UShort)
                (
                (offset + nbytes) < ALIGN(offset, 8) + 8
                    ?
                    (nbytes <= 8) ? 0x01u :
                    (nbytes == 16) ? 0b11u :
                    0b1111u
                    :
                    (nbytes <= 8) ? 0b11u :
                    (nbytes == 16) ? 0b111u :
                    0b11111u
                ) << ((offset >> 3) & 7);
            
        }

        template<> inline void write<1>(int offset) { m_flag[offset >> 6] |= 1 << ((offset >> 3) & 7); }



        inline UInt get_count() {
            UInt write_count = 0;
            for (auto offset : *this) {
                write_count += 1;
            }
            return write_count;
        }

        //写入遍历器
        class iterator
        {
        private:
            UInt _pcur;
            UInt m_len;
            ULong* m_flag;
        public:
            inline iterator(UChar* flag) :_pcur(0), m_flag((ULong*)flag), m_len(0) {
                DWORD N;
                for (; ; _pcur += 64) {
                    if (_BitScanForward64(&N, m_flag[_pcur >> 6])) {
                        _pcur += N;
                        return;
                    }
                }
            }
            iterator(UChar* flag, UInt length) :
                _pcur(length >> 3),
                m_flag((ULong*)flag),
                m_len(length)
            {}
            inline bool operator!=(const iterator& src)
            {
                return (_pcur << 3) < src.m_len;
            }

            inline void operator++()
            {
                unsigned long N;
                for (;;) {
                    if (_BitScanForward64(&N, m_flag[_pcur >> 6] & fastMaskReverse(_pcur % 64))) {
                        _pcur = ALIGN(_pcur, 64) + N;
                        return;
                    }
                    else {
                        _pcur = ALIGN(_pcur + 64, 64);
                    }
                }
            }

            inline int operator*()
            {
                return (_pcur++) << 3;
            }
        };

        inline iterator begin() {
            return iterator(m_flag);
        }

        inline iterator end() {
            return iterator(m_flag, maxlength);
        }
    };



    //Register<maxlength>


#define GET_from_nbytes(nbytes, ... )    \
((nbytes)==1)? \
    GET1(__VA_ARGS__): \
    ((nbytes)==2)? \
        GET2(__VA_ARGS__):\
        ((nbytes)==4)? \
            GET4(__VA_ARGS__):\
            ((nbytes)==8)? \
                GET8(__VA_ARGS__):\
                GET1(23333)//imPOSSIBLE

    class RegisterStatic {
        static __m256i m32_fast[33];
        static __m256i m32_mask_reverse[33];
    protected:
        RegisterStatic();
        static void setfast(void* fast_ptr, UInt __nbytes);
    };

    template<int maxlength>
    class Register : protected RegisterStatic {
        z3::vcontext& m_ctx;
        Symbolic<maxlength>* symbolic;
        Record<maxlength>* record;
        __declspec(align(32))
        UChar m_bytes[maxlength];

        template<typename _> friend class MEM;
        template<typename _> friend class State;
    public:

        inline Register(z3::vcontext& ctx, Bool _need_record) :
            m_ctx(ctx),
            symbolic(NULL),
            record(_need_record ? new Record<maxlength>() : NULL)
        { }
        //翻译转换父register
        inline Register(Register<maxlength>& father_regs, z3::vcontext& ctx, Bool _need_record) :
            m_ctx(ctx),
            symbolic(father_regs.symbolic ? new Symbolic<maxlength>(m_ctx, father_regs.symbolic) : NULL),
            record(_need_record ? new Record<maxlength>() : NULL)
        {
            memcpy(m_bytes, father_regs.m_bytes, maxlength);
        }

        ~Register<maxlength>() {
            if (symbolic) delete symbolic;
            if (record) delete record;
        };

        void clearRecord() { if (record) record->clearRecord(); };
        inline Record<maxlength>* getRecord() { return record; }


        template<int n>
        inline bool fast_check(UInt offset);
        template<> inline bool fast_check<8>(UInt offset) { return *(int8_t*)(symbolic->m_fastindex + offset); };
        template<> inline bool fast_check<16>(UInt offset) { return *(int16_t*)(symbolic->m_fastindex + offset); };
        template<> inline bool fast_check<32>(UInt offset) { return *(int32_t*)(symbolic->m_fastindex + offset); };
        template<> inline bool fast_check<64>(UInt offset) { return *(int64_t*)(symbolic->m_fastindex + offset); };
        template<> inline bool fast_check<128>(UInt offset) { return sse_check_zero_X128(symbolic->m_fastindex + offset); };
        template<> inline bool fast_check<256>(UInt offset) { return sse_check_zero_X256(symbolic->m_fastindex + offset); };


        template<int n>
        inline void fast_set_zero(UInt offset);
        template<> inline void fast_set_zero<8>(UInt offset) { *(int8_t*)(symbolic->m_fastindex + offset) = 0; };
        template<> inline void fast_set_zero<16>(UInt offset) { *(int16_t*)(symbolic->m_fastindex + offset) = 0; };
        template<> inline void fast_set_zero<32>(UInt offset) { *(int32_t*)(symbolic->m_fastindex + offset) = 0; };
        template<> inline void fast_set_zero<64>(UInt offset) { *(int64_t*)(symbolic->m_fastindex + offset) = 0; };
        template<> inline void fast_set_zero<128>(UInt offset) { _mm_storeu_si128((__m128i*) & symbolic->m_fastindex[offset], _mm_setzero_si128()); };
        template<> inline void fast_set_zero<256>(UInt offset) { _mm256_storeu_si256((__m256i*) & symbolic->m_fastindex[offset], _mm256_setzero_si256()); };


        template<int n>
        inline void fast_set(UInt offset);
        template<> inline void fast_set<8>(UInt offset) { *(int8_t*)(symbolic->m_fastindex + offset) = 0x01; };
        template<> inline void fast_set<16>(UInt offset) { *(int16_t*)(symbolic->m_fastindex + offset) = 0x0201; };
        template<> inline void fast_set<32>(UInt offset) { *(int32_t*)(symbolic->m_fastindex + offset) = 0x04030201; };
        template<> inline void fast_set<64>(UInt offset) { *(int64_t*)(symbolic->m_fastindex + offset) = 0x0807060504030201; };
        template<> inline void fast_set<128>(UInt offset) { _mm_storeu_si128((__m128i*) & symbolic->m_fastindex[offset], _mm_set_epi64x(0x100f0e0d0c0b0a09, 0x0807060504030201)); };
        template<> inline void fast_set<256>(UInt offset) { _mm256_storeu_si256((__m256i*) & symbolic->m_fastindex[offset], _mm256_set_epi64x(0x201f1e1d1c1b1a19, 0x1817161514131211, 0x100f0e0d0c0b0a09, 0x0807060504030201)); };


        template<int nbytes, TASSERT(nbytes <= 8)>
        inline Z3_ast reg2Ast(UInt offset) {
            return Reg2Ast((int)nbytes, &m_bytes[offset], &symbolic->m_fastindex[offset], symbolic->m_ast + offset, m_ctx);
        }

        template<int nbytes, TASSERT(nbytes > 8)>
        inline Z3_ast reg2Ast(UInt offset) {
            return Reg2AstSSE((int)nbytes, &m_bytes[offset], &symbolic->m_fastindex[offset], symbolic->m_ast + offset, m_ctx);
        }

        template<int nbytes, TASSERT(nbytes <= 8)>
        inline Z3_ast reg2Ast(UInt offset, z3::vcontext& toctx) {
            return Reg2Ast((int)nbytes, &m_bytes[offset], &symbolic->m_fastindex[offset], symbolic->m_ast + offset, m_ctx, toctx);
        }

        template<int nbytes, TASSERT(nbytes > 8)>
        inline Z3_ast reg2Ast(UInt offset, z3::vcontext& toctx) {
            return Reg2AstSSE((int)nbytes, &m_bytes[offset], &symbolic->m_fastindex[offset], symbolic->m_ast + offset, m_ctx, toctx);
        }

        //-------------------------------- get --------------------------------------

        template<bool sign, int nbits, sv::z3sk sk, TASSERT(sk == Z3_BV_SORT)>
        inline sv::rsval<sign, nbits, sk> get(UInt offset) {
            if (symbolic && fast_check<nbits>(offset)) {
                return sv::rsval<sign, nbits, Z3_BV_SORT>(m_ctx, reg2Ast< (nbits >> 3) >(offset), no_inc{});
            }
            else {
                return sv::rsval<sign, nbits, Z3_BV_SORT>(m_ctx, &m_bytes[offset]);
            }
        }

        template<bool sign, int nbits, sv::z3sk sk, TASSERT(sk == Z3_FLOATING_POINT_SORT)>
        inline sv::rsval<sign, nbits, sk> get(UInt offset) {
            if (symbolic && fast_check<nbits>(offset)) {
                return sv::symbolic<sign, nbits, Z3_BV_SORT>(m_ctx, reg2Ast< (nbits >> 3) >(offset), no_inc{}).tofpa();
            }
            else {
                return sv::rsval<sign, nbits, Z3_FLOATING_POINT_SORT>(m_ctx, &m_bytes[offset]);
            }
        }

        template<IRType ty, class _svc = sv::IRty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> get(UInt offset) { return get<_svc::is_signed, _svc::nbits, _svc::sk>(offset); }

        template<typename ty, TASSERT(std::is_arithmetic<ty>::value), class _svc = sv::sv_cty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> get(UInt offset) { return get<_svc::is_signed, _svc::nbits, _svc::sk>(offset); }



        //-------------------------------- translate get --------------------------------------

        template<bool sign, int nbits, sv::z3sk sk, TASSERT(sk == Z3_BV_SORT)>
        inline sv::rsval<sign, nbits, sk> get(UInt offset, z3::vcontext& ctx) {
            if (symbolic && fast_check<nbits>(offset)) {
                return sv::rsval<sign, nbits, Z3_BV_SORT>(ctx, reg2Ast< (nbits >> 3) >(offset, ctx), no_inc{});
            }
            else {
                return sv::rsval<sign, nbits, sk>(ctx, &m_bytes[offset]);
            }
        }

        template<bool sign, int nbits, sv::z3sk sk, TASSERT(sk == Z3_FLOATING_POINT_SORT)>
        inline sv::rsval<sign, nbits, sk> get(UInt offset, z3::vcontext& ctx) {
            if (symbolic && fast_check<nbits>(offset)) {
                return sv::symbolic<sign, nbits, Z3_BV_SORT>(ctx, reg2Ast< (nbits >> 3) >(offset, ctx), no_inc{}).tofpa();
            }
            else {
                return sv::rsval<sign, nbits, sk>(ctx, &m_bytes[offset]);
            }
        }

        template<typename ty, TASSERT(std::is_arithmetic<ty>::value), class _svc = sv::sv_cty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> get(UInt offset, z3::vcontext& ctx) { return get<_svc::is_signed, _svc::nbits, _svc::sk>(offset, ctx); }

        template<IRType ty, class _svc = sv::IRty<ty>>
        inline sv::rsval<_svc::is_signed, _svc::nbits, _svc::sk> get(UInt offset, z3::vcontext& ctx) { return get<_svc::is_signed, _svc::nbits, _svc::sk>(offset, ctx); }





        //---------------------------------------------- set numreal ---------------------------------------------------


        template<typename DataTy, TASSERT(std::is_arithmetic<DataTy>::value && !sv::is_sse<DataTy>::value)>
        void set(UInt offset, DataTy data) {
            if (symbolic && fast_check<(sizeof(data) << 3)>(offset)) {
                clear(offset, sizeof(DataTy));
                fast_set_zero<(sizeof(DataTy) << 3)>(offset);
            }
            *(DataTy*)(m_bytes + offset) = data;
            if (record)  record->write<sizeof(DataTy)>(offset);
        }


        //simd 128
        template<typename DataTy, TASSERT(sizeof(DataTy) == 16 && sv::is_sse<DataTy>::value)>
        void set(UInt offset, const DataTy& data) {
            if (symbolic && fast_check<128>(offset)) {
                clear(offset, 16);
                fast_set_zero<128>(offset);
            }
            _mm_storeu_si128((__m128i*)(m_bytes + offset), _mm_loadu_si128((__m128i*) & data));
            if (record)  record->write<16>(offset);
        }

        //simd 256
        template<typename DataTy, TASSERT(sizeof(DataTy) == 32 && sv::is_sse<DataTy>::value)>
        void set(UInt offset, const DataTy& data) {
            if (symbolic && fast_check<256>(offset)) {
                clear(offset, 32);
                fast_set_zero<256>(offset);
            }
            _mm256_storeu_si256((__m256i*)(m_bytes + offset), _mm256_loadu_si256((__m256i*) & data));
            if (record)  record->write<32>(offset);
        }

        template<bool sign, int nbits, TASSERT(nbits <= 64)>
        inline void set(UInt offset, const sv::ctype_val<sign, nbits, Z3_BV_SORT>& data) {
            set(offset, data.value());
        }

        //---------------------------------------------- set ast ---------------------------------------------------

        // only n_bit 8, 16, 32, 64 ,128 ,256
        template<int nbits>
        inline void set(UInt offset, Z3_ast _ast) {
            if (!symbolic) 
                symbolic = new Symbolic<maxlength>(m_ctx);
            if (fast_check<nbits>(offset)) {
                clear(offset, (nbits >> 3));
            }
            fast_set<nbits>(offset);
            symbolic->m_ast[offset] = _ast;
            Z3_inc_ref(m_ctx, _ast);
            if (record)
                record->write<(nbits >> 3)>(offset);
        }
        
        template<bool sign, int nbits>
        inline void set(UInt offset, const sv::symbolic<sign, nbits, Z3_BV_SORT>& data) {
            set<nbits>(offset, (Z3_ast)data);
        }


        template<bool sign, int nbits>
        inline void set(UInt offset, const sv::rsval<sign, nbits, Z3_BV_SORT>& data) {
            if (data.real()) {
                set(offset, data.tor());
            }else{
                set(offset, data.tos());
            }
        }


        inline void set(UInt offset, const tval& data) {
            if (data.real()) {

            }
            else {

            }
        }

        //---------------------------------------------- Iex_Get ---------------------------------------------------



        // IRType or nbit
        tval Iex_Get(UInt offset, IRType ty) {
            switch (ty) {
#define lazydef(vectype,nbit)                                \
    case Ity_##vectype##nbit:                                \
        return     get<Ity_##vectype##nbit>(offset);
            lazydef(I, 8);
            lazydef(I, 16);
            lazydef(F, 32);
            lazydef(I, 32);
            lazydef(F, 64);
            lazydef(I, 64);
            lazydef(V, 128);
            lazydef(I, 128);
            lazydef(V, 256);
#undef lazydef
            default: 
                vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
            }
            return tval();
        }


        //---------------------------------------------- Iex_Get TRANSLATE ---------------------------------------------------

        //ty = (IRType)nbits or IRType
        inline tval Iex_Get(UInt offset, IRType ty, z3::vcontext& ctx) {
            switch (ty) {
#define lazydef(vectype,nbit)                                   \
    case Ity_##vectype##nbit:                                   \
        return     get<Ity_##vectype##nbit>(offset, ctx);
            lazydef(I, 8);
            lazydef(I, 16);
            lazydef(F, 32);
            lazydef(I, 32);
            lazydef(F, 64);
            lazydef(I, 64);
            lazydef(V, 128);
            lazydef(I, 128);
            lazydef(V, 256);
#undef lazydef
            default: vex_printf("ty = 0x%x\n", (UInt)ty); vpanic("tIRType");
            }
            return Vns();
        }


        //---------------------------------------------- Ist_Put ---------------------------------------------------

        inline void Ist_Put(UInt offset, tval const& ir) {
            if (ir.symb()) {
                switch (ir.nbits()) {
                case 8: set(offset, ir.tos<true, 8, Z3_BV_SORT>()); break;
                case 16:set(offset, ir.tos<true, 16, Z3_BV_SORT>()); break;
                case 32:set(offset, ir.tos<true, 32, Z3_BV_SORT>()); break;
                case 64:set(offset, ir.tos<true, 64, Z3_BV_SORT>()); break;
                case 128:set(offset, ir.tos<true, 128, Z3_BV_SORT>()); break;
                case 256:set(offset, ir.tos<true, 256, Z3_BV_SORT>()); break;
                default:
                    VPANIC("error");
                }
            }
            else {
                switch (ir.nbits()) {
                case 8: set(offset, (UChar)ir); break;
                case 16:set(offset, (UShort)ir); break;
                case 32:set(offset, (UInt)ir); break;
                case 64:set(offset, (ULong)ir); break;
                case 128:set(offset, (__m128i)ir); break;
                case 256:set(offset, (__m256i)ir); break;
                default:
                    VPANIC("error");
                }
            }
        }

#define m_fastindex symbolic->m_fastindex
#define m_ast symbolic->m_ast

        //  slowly
        void Ist_Put(UInt offset, void* data, UInt nbytes) {
            vassert(offset + nbytes <= maxlength);
            if (symbolic) { clear(offset, nbytes); memset(m_fastindex + offset, 0, nbytes); };
            memcpy(m_bytes + offset, data, nbytes);
            if (record) {
                auto _nbytes = nbytes;
                while (_nbytes) {
                    if (_nbytes >= 8) { _nbytes -= 8; record->write<8>(offset + _nbytes); }
                    else if (_nbytes >= 4) { _nbytes -= 4; record->write<4>(offset + _nbytes); }
                    else if (_nbytes >= 2) { _nbytes -= 2; record->write<2>(offset + _nbytes); }
                    else { _nbytes--; record->write<1>(offset + _nbytes); }
                }
            }
        }

        // slowly
        void Ist_Put(UInt offset, Z3_ast _ast, UInt nbytes) {
            if (!symbolic)
                symbolic = new Symbolic<maxlength>(m_ctx);
            clear(offset, nbytes);
            auto fastindex = m_fastindex + offset;
            for (int i = 0; i < nbytes; i++) { SET1(fastindex + i, i + 1); };
            m_ast[offset] = _ast;
            Z3_inc_ref(m_ctx, _ast);
            if (record) {
                auto _nbytes = nbytes;
                while (_nbytes) {
                    if (_nbytes >= 8) { _nbytes -= 8; record->write<8>(offset + _nbytes); }
                    else if (_nbytes >= 4) { _nbytes -= 4; record->write<4>(offset + _nbytes); }
                    else if (_nbytes >= 2) { _nbytes -= 2; record->write<2>(offset + _nbytes); }
                    else { _nbytes--; record->write<1>(offset + _nbytes); }
                }
            }
        }



        //is slowly 
        tval Iex_Get(UInt offset, UInt nbytes) {
            vassert(nbytes <= 32);
            if (this->symbolic) {
                auto fastindex = m_fastindex + offset;
                auto _nbytes = nbytes;
                while (_nbytes) {
                    if (_nbytes >= 8) { _nbytes -= 8; if (GET8(fastindex + _nbytes)) { goto has_sym; }; }
                    else if (_nbytes >= 4) { _nbytes -= 4; if (GET4(fastindex + _nbytes)) { goto has_sym; }; }
                    else if (_nbytes >= 2) { _nbytes -= 2; if (GET2(fastindex + _nbytes)) { goto has_sym; }; }
                    else { _nbytes--; if (GET1(fastindex + _nbytes)) { goto has_sym; }; }
                };

            }
            return tval(m_ctx, GET32(m_bytes + offset), nbytes << 3);
        has_sym:
            return tval(m_ctx, Reg2AstSSE(nbytes, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx), nbytes << 3, no_inc{});
        }

        //is slowly 变长取值
        tval Iex_Get(UInt offset, UInt nbytes, z3::vcontext& ctx) {
            vassert(nbytes <= 32);
            auto fastindex = m_fastindex + offset;
            auto _nbytes = nbytes;
            while (_nbytes) {
                if (_nbytes >= 8) { _nbytes -= 8; if (GET8(fastindex + _nbytes)) { goto has_sym; }; }
                else if (_nbytes >= 4) { _nbytes -= 4; if (GET4(fastindex + _nbytes)) { goto has_sym; }; }
                else if (_nbytes >= 2) { _nbytes -= 2; if (GET2(fastindex + _nbytes)) { goto has_sym; }; }
                else { _nbytes--; if (GET1(fastindex + _nbytes)) { goto has_sym; }; };
            }
            return tval(ctx, GET32(m_bytes + offset), nbytes << 3);
        has_sym:
            return tval(ctx, Reg2AstSSE(nbytes, m_bytes + offset, m_fastindex + offset, m_ast + offset, m_ctx, ctx), nbytes << 3, no_inc{});
        }


        //将fastindex offset位置的ast清空（剪切&释放）
        void clear(UInt org_offset, Int LEN)
        {
            Char length = LEN;
            char fastR = m_fastindex[org_offset + length] - 1;
            if (fastR > 0) {
                auto index = org_offset + length - fastR;
                auto sort_size = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast[index]));

                auto AstR = Z3_mk_extract(m_ctx, sort_size - 1, (fastR << 3), m_ast[index]);
                Z3_inc_ref(m_ctx, AstR);
                m_ast[org_offset + length] = AstR;
                setfast(m_fastindex + org_offset + length, (sort_size >> 3) - fastR);
                if (fastR > length) {
                    auto AstL = Z3_mk_extract(m_ctx, ((fastR - length) << 3) - 1, 0, m_ast[index]);
                    Z3_inc_ref(m_ctx, AstL);
                    Z3_dec_ref(m_ctx, m_ast[index]);
                    m_ast[index] = AstL;
                    return;
                }
                else if (fastR == length) {
                    Z3_dec_ref(m_ctx, m_ast[index]);
                    return;
                }
                length -= fastR;
                Z3_dec_ref(m_ctx, m_ast[index]);
            }
            char fastL = m_fastindex[org_offset] - 1;
            if (fastL > 0) {
                auto index = org_offset - fastL;
                auto sort_size = Z3_get_bv_sort_size(m_ctx, Z3_get_sort(m_ctx, m_ast[index])) >> 3;
                auto newAst = Z3_mk_extract(m_ctx, ((fastL) << 3) - 1, 0, m_ast[index]);
                Z3_inc_ref(m_ctx, newAst);
                Z3_dec_ref(m_ctx, m_ast[index]);
                m_ast[index] = newAst;
                org_offset += (sort_size - fastL);
                length -= (sort_size - fastL);
            }
            DWORD index;
            if (LEN <= 8) {
                ULong fast_index = GET8(m_fastindex + org_offset);
                while (length > 0) {
                    if (_BitScanReverse64(&index, fast_index & fastMaskB(length))) {
                        index >>= 3;
                        auto fast = m_fastindex[org_offset + index] - 1;
                        length = index - fast;
                        Z3_dec_ref(m_ctx, m_ast[org_offset + length]);
                    }
                    else {
                        return;
                    }
                }
            }
            else {
                // It's fast for CPU to reads data from aligned addresses .
                UInt _pcur = org_offset + length - 1;
                if (_pcur < org_offset)
                    return;
                for (; ; ) {
                    if (_BitScanReverse64(&index, ((DWORD64*)(m_fastindex))[_pcur >> 3] & fastMaskBI1(_pcur % 8))) {
                        _pcur = ALIGN(_pcur, 8) + (index >> 3);
                        _pcur = _pcur - m_fastindex[_pcur] + 1;
                        if (_pcur >= org_offset)
                            Z3_dec_ref(m_ctx, m_ast[_pcur]);
                        else
                            return;
                        _pcur--;
                    }
                    else {
                        _pcur = ALIGN(_pcur - 8, 8) + 7;
                        if (_pcur < org_offset)
                            return;
                    }
                }
            }
        }

        inline void write_regs(int offset, void* addr, int length) {
            memcpy(m_bytes + offset, addr, length);
        }

        inline void read_regs(int offset, void* addr, int length) {
            memcpy(addr, m_bytes + offset, length);
        }


    private:
        inline void Ist_Put(UInt, Z3_ast) = delete;
        inline void Ist_Put(UInt, Z3_ast&) = delete;
        inline void set(UInt, Z3_ast) = delete;
        inline void set(UInt, Z3_ast&) = delete;
        Register(const Register<maxlength>& father_regs) = delete;
        void operator = (Register<maxlength>& a) = delete;
    };

};


#ifndef UNDEFREG
#undef registercodedef
#undef GETASTSIZE
#undef GET_from_nbytes
#undef B32_Ist_Put
#undef B16_Ist_Put
#endif

#undef m_fastindex
#undef m_ast

#endif //REGISTER_HL
