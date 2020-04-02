#include "engine/addressing_mode.h"
#include <intrin.h>    //(include immintrin.h)

#define fastMask(n) ((ULong)((((int)(n))<64)?((1ull << ((int)(n))) - 1):-1ll))
#define fastMaskI1(n) fastMask(((n)+1))
#define fastMaskReverseI1(N) (~fastMaskI1(N))
using namespace z3;


extern "C" void vex_assert_fail(const HChar * expr, const HChar * file, Int line, const HChar * fn);
extern "C" unsigned int vex_printf(const HChar * format, ...);
extern "C" void vpanic(const HChar * str);

template<typename ADDR>
TR::addressingMode<ADDR>::addressingMode(const expr& e)
    :
    m_ctx(e.ctx()),
    m_symbolic(e),
    m_offset(m_ctx),
    m_sym_mask(0ull),
    m_sym_mask_n(0),
    m_or_mask(0ull)
{
    if (ast2baseAoffset()) {
        if (offset_bit_blast()) {
            m_analysis_kind = addressingMode::support_bit_blast;
        }
        else {
            m_analysis_kind = addressingMode::found_base_and_offset;
        }
    }
    else {
        m_analysis_kind = addressingMode::cant_analysis;
    }
}
template<typename ADDR>
TR::addressingMode<ADDR>::iterator::iterator(TR::addressingMode<ADDR>& am) :
    m_sym_mask(am.m_sym_mask),
    m_or_mask(am.m_or_mask),
    tmp_bit_blast((ADDR)0),
    tmp_target_bit_blast((ADDR)0),
    m_sym_ml_n(0),
    m_sign_ml_n(0)
{
    unsigned long N;
    UInt _pcur;
    UInt nb = 0;

    if (_BitScanForward64(&N, m_sym_mask)) {
        m_sym_ml[0] = shift_mask{ (UChar)N,((ADDR)1) << N };
        m_sym_ml_n = 1;
        _pcur = N;
        tmp_target_bit_blast = ((ADDR)1);
        nb = 1;

        for (; ; ) {
            if (_BitScanForward64(&N, m_sym_mask & fastMaskReverseI1(_pcur))) {
                if (N = _pcur + 1) {
                    m_sym_ml[m_sym_ml_n - 1].mask |= ((ADDR)1) << N;
                }
                else {
                    m_sym_ml[m_sym_ml_n - 1] = shift_mask{ (UChar)N,((ADDR)1) << N };
                    m_sym_ml_n++;
                }
                tmp_target_bit_blast |= ((ADDR)1) << (nb++);
                _pcur = N;
            }
            else {
                break;
            }
        }
    }

parse_sign:
    for (auto s : am.m_sign_mask) {
        m_sign_ml[m_sign_ml_n++] = shift_mask{ (UChar)nb, s };
        tmp_target_bit_blast |= ((ADDR)1) << (nb++);
    }
    tmp_target_bit_blast += 1;
}



















//a=b+c+d+e...+z -> b c d e
template<typename ADDR>
void TR::addressingMode<ADDR>::_offset2opAdd(std::deque<expr>& ret, expr const& _e)
{
    expr e = _e;
    context& c = e.ctx();
    if (e.kind() == Z3_APP_AST) {
        func_decl f = e.decl();
        switch (f.decl_kind())
        {
        case Z3_OP_BADD: {
            auto max = e.num_args();
            for (UInt i = 0; i < max; i++) {
                _offset2opAdd(ret, e.arg(i));
            }
            return;
        }
        case Z3_OP_BSUB: {
            auto max = e.num_args();
            for (UInt i = 0; i < max; i++) {
                if (i == 0) {
                    _offset2opAdd(ret, e.arg(i));
                }
                else {
                    _offset2opAdd(ret, -e.arg(i));
                }
            }
            return;
        }
        }
        ret.emplace_back(e);
        return;
    }
}

template<typename ADDR>
bool TR::addressingMode<ADDR>::_check_add_no_overflow(expr const& e1, expr const& e2) {
    UInt bs = e1.get_sort().bv_size();
    bool bit_jw = false;
    /*  std::cout << e1 << std::endl;
      std::cout << e2 << std::endl;*/
    for (UInt i = 0; i < bs; i++) {
        addressingMode::sbit_struct ss0 = addressingMode::_check_is_extract(e1, i);
        addressingMode::sbit_struct ss1 = addressingMode::_check_is_extract(e2, i);
        bool b0 = (ss0.sym_ast) ? true : ss0.rbit;
        bool b1 = (ss1.sym_ast) ? true : ss1.rbit;

        if (b0 ^ b1) {}
        else {
            if (b0 && b1) {
                bit_jw = true;
            }
            else {
                bit_jw = false;
            }
        }
    }
    return !bit_jw;
}


template<typename ADDR>
bool TR::addressingMode<ADDR>::ast2baseAoffset()
{
    //std::cout << saddr.simplify() << std::endl << std::endl;
    z3::expr base = z3::expr(m_ctx);
    m_offset = _ast2base(base, m_symbolic, 0, 6);
    //std::cout << idx << std::endl;
    ULong _m_base;
    if ((Z3_ast)base) {
        if (base.simplify().is_numeral_u64(_m_base)) {
            m_base = _m_base;
#if defined(NEED_VERIFY)
            if (m_base > 100) {
                Int is_right;
                z3::expr eval = base + m_offset == m_symbolic;
                if (z3::ite(eval, m_ctx.bv_val(1, 8), m_ctx.bv_val(0, 8)).simplify().is_numeral_i(is_right)) {
                    if (is_right) {
                        return true;
                    }
                    else {
                        goto faild;
                    }
                }
                else {
                    vex_printf("cant determine base %p try solver:\n", m_base);
                }
                z3::solver s(m_ctx);
                s.add(!eval);
                if (s.check() == z3::unsat) {
                    return true;
                }
                std::cout << "unsat model:\n" << s.get_model() << std::endl;
                goto faild;
            }
#else
            return true;
#endif
        }
    }
    return false;
faild:
    std::cout << "symbolic:\n" << m_symbolic << std::endl << std::endl;
    std::cout << "symbolic.simplify:\n" << m_symbolic.simplify() << std::endl << std::endl;

    std::cout << "base:\n" << m_base << std::endl << std::endl;
    std::cout << "Index:\n" << m_offset << std::endl << std::endl;

    vex_printf("is False  %p\n", m_base);
    vpanic("sorry .engine error.  report me and i will fix it\n");
}

template<typename ADDR>
bool TR::addressingMode<ADDR>::offset_bit_blast()
{
    z3::sort so = m_offset.get_sort();
    UInt size = so.bv_size();

    std::deque<sbit_struct_r> vec;
    for (UInt idx = 0; idx < size; idx++) {
        sbit_struct s = _check_is_extract(m_offset, idx);
        //把ast分解为 一个一个bit独立单元
        if (s.sym_ast) {
            auto end = vec.end();
            auto m = vec.begin();
            bool exist = false;
            while (m != end) {
                if (s.sym_ast == m->sbit.sym_ast && s.idx == m->sbit.idx) {
                    m->sign_mask |= ((ADDR)1) << idx;
                    m->nbit++;
                    exist = true;
                    break;
                }
                m++;
            };
            if (!exist) {
                vec.emplace_back(sbit_struct_r{ s  , ((ADDR)1) << idx, 1 });
            };
        }
        else {
            m_or_mask = m_or_mask | ((ADDR)s.rbit << idx);
        }
    }


    auto end = vec.end();
    auto m = vec.begin();
    while (m != end) {
        if (m->nbit == 1) {
            m_sym_mask |= m->sign_mask;
            m_sym_mask_n++;
        }
        else {
            m_sign_mask.emplace_back(m->sign_mask);
        }
        m++;
    }
    return ((m_sym_mask_n + m_sign_mask.size()) >= BIT_BLAST_MAX_BIT) ? false : true;
}

template<typename ADDR>
void TR::addressingMode<ADDR>::print()
{
    printf("\tor_mask: %016x\t\t", m_or_mask);
    printf("sym_mask: n:%d %016x\n", m_sym_mask_n, m_sym_mask);
    if (!m_sign_mask.empty()) {
        printf("sign_mask: \n\t{\n", m_or_mask);
        for (auto sm : m_sign_mask) {
            printf("\t\t %016x\n", sm);
        }
        printf("\n\t}\n", m_or_mask);
    }
}

// ast(symbolic address) = numreal(base) + symbolic(offset) 
template<typename ADDR>
expr TR::addressingMode<ADDR>::_ast2base(expr& base,
    expr const& e,
    UInt deep, UInt max_deep
) {
    context& c = e.ctx();
    if (deep < max_deep) {
        if (e.kind() == Z3_APP_AST) {
            func_decl f = e.decl();
            switch (f.decl_kind())
            {
            case Z3_OP_BADD: {
                expr idx_sum(c);
                auto max = e.num_args();
                for (UInt i = 0; i < max; i++) {
                    expr arg1(c);
                    expr idx = _ast2base(arg1, e.arg(i), deep + 1, max_deep);
                    if ((Z3_ast)idx) {
                        if ((Z3_ast)idx_sum) {
                            idx_sum = idx_sum + idx;
                        }
                        else {
                            idx_sum = idx;
                        }
                    }
                    if ((Z3_ast)arg1) {
                        if ((Z3_ast)base) {
                            base = base + arg1;
                        }
                        else {
                            base = arg1;
                        }
                    }
                }
                return idx_sum;
            }
            case Z3_OP_BSUB: {
                expr idx_sum(c);
                auto max = e.num_args();
                for (UInt i = 0; i < max; i++) {
                    expr arg1(c);
                    expr idx = _ast2base(arg1, e.arg(i), deep + 1, max_deep);
                    if ((Z3_ast)idx) {
                        if ((Z3_ast)idx_sum) {
                            idx_sum = idx_sum - idx;
                        }
                        else {
                            if (i == 0) {
                                idx_sum = idx;
                            }
                            else {
                                idx_sum = -idx;
                            }
                        }
                    }
                    if ((Z3_ast)arg1) {
                        if ((Z3_ast)base) {
                            base = base - arg1;
                        }
                        else {
                            if (i == 0) {
                                base = arg1;
                            }
                            else {
                                base = -arg1;
                            }
                        }
                    }
                }
                return idx_sum;
            }
            case Z3_OP_SIGN_EXT: {
                uint64_t extn = Z3_get_decl_int_parameter(c, f, 0);
                expr arg1(c);
                expr idx1 = _ast2base(arg1, e.arg(0), deep + 1, max_deep);
                if ((Z3_ast)arg1) {
                    if ((Z3_ast)idx1) {
                        UInt bs = idx1.get_sort().bv_size();
                        if (_check_add_no_overflow(idx1.extract(bs - 2, 0), arg1.extract(bs - 2, 0))) {
                            addressingMode::sbit_struct ss0 = addressingMode::_check_is_extract(idx1, bs - 1);
                            addressingMode::sbit_struct ss1 = addressingMode::_check_is_extract(arg1, bs - 1);
                            bool b0 = (ss0.sym_ast) ? true : ss0.rbit;
                            bool b1 = (ss1.sym_ast) ? true : ss1.rbit;
                            if ((!b0) || (!b1)) {
                                base = sext(arg1, extn);
                                return sext(idx1, extn);
                            }
                        }
                        goto goFaild;
                    }
                    else {
                        base = sext(arg1, extn);
                        return expr(c);
                    }
                }
                else {
                    base = expr(c);
                    if ((Z3_ast)idx1) {
                        return sext(idx1, extn);
                    }
                    else {
                        goto goFaild;
                    }
                }
            }

            case Z3_OP_ZERO_EXT: {
                uint64_t extn = Z3_get_decl_int_parameter(c, f, 0);
                expr arg1(c);
                expr idx1 = _ast2base(arg1, e.arg(0), deep + 1, max_deep);
                if ((Z3_ast)arg1) {
                    if ((Z3_ast)idx1) {
                        if (_check_add_no_overflow(idx1, arg1)) {
                            base = zext(arg1, extn);
                            return zext(idx1, extn);
                        }
                        goto goFaild;
                    }
                    else {
                        base = zext(arg1, extn);
                        return expr(c);
                    }
                }
                else {
                    base = expr(c);
                    if ((Z3_ast)idx1) {
                        return zext(idx1, extn);
                    }
                    else {
                        goto goFaild;
                    }
                }
            }
            case Z3_OP_EXTRACT: {
                UInt lo = e.lo();
                UInt hi = e.hi();
                expr arg1(c);
                expr idx1 = _ast2base(arg1, e.arg(0), deep + 1, max_deep);
                if ((Z3_ast)arg1) {
                    base = arg1.extract(hi, lo);
                }
                else {
                    base = expr(c);
                }
                if ((Z3_ast)idx1) {
                    return idx1.extract(hi, lo);
                }
                else {
                    return expr(c);
                }
            }
            case Z3_OP_CONCAT: {
                expr idx_sum(c);
                auto max = e.num_args();
                for (UInt i = 0; i < max; i++) {
                    expr arg1(c);
                    expr idx = _ast2base(arg1, e.arg(i), deep + 1, max_deep);
                    UInt LL = ((Z3_ast)arg1) ? arg1.get_sort().bv_size() : idx.get_sort().bv_size();
                    if (i != 0) {
                        if ((Z3_ast)idx && (Z3_ast)arg1) {
                            goto goFaild;
                        }
                    }

                    if ((Z3_ast)idx) {
                        if ((Z3_ast)idx_sum) {
                            idx_sum = concat(idx_sum, idx);
                        }
                        else {
                            idx_sum = idx;
                        }
                    }
                    else {
                        if ((Z3_ast)idx_sum) {
                            idx_sum = concat(idx_sum, c.bv_val(0, LL));
                        }
                        else {
                            idx_sum = c.bv_val(0, LL);
                        }
                    }

                    if ((Z3_ast)arg1) {
                        if ((Z3_ast)base) {
                            base = concat(base, arg1);
                        }
                        else {
                            base = arg1;
                        }
                    }
                    else {
                        if ((Z3_ast)base) {
                            base = concat(base, c.bv_val(0, LL));
                        }
                        else {
                            base = c.bv_val(0, LL);
                        }
                    }
                }

                return idx_sum;
            }
            default:
                break;
            }
        }
        else if (e.is_quantifier()) {
        }
        else if (e.is_numeral()) {
            base = e;
            return expr(c);
        }
        else {
        }
    }
goFaild:
    base = expr(c);;
    return e;
}


template<typename ADDR>
TR::addressingMode<ADDR>::sbit_struct TR::addressingMode<ADDR>::_check_is_extract(expr const& _e, UInt _idx) {
    context& c = _e.ctx();
    UInt idx = _idx;
    expr e = _e;
    //std::cout << e;
    while (True) {
        sort so = e.get_sort();
        UInt size = so.bv_size();
        if (e.kind() == Z3_APP_AST) {
            func_decl f = e.decl();
            switch (f.decl_kind())
            {
            case Z3_OP_SIGN_EXT: {
                uint64_t extn = Z3_get_decl_int_parameter(c, f, 0);
                e = e.arg(0);
                if (idx >= (size - extn)) {
                    idx = (size - extn) - 1;
                }
                break;
            }

            case Z3_OP_ZERO_EXT: {
                uint64_t extn = Z3_get_decl_int_parameter(c, f, 0);
                if (idx >= (size - extn)) {
                    return sbit_struct{ NULL, false, 0 };
                }
                else {
                    e = e.arg(0);
                }
                break;
            }

            case Z3_OP_EXTRACT: {
                UInt lo = e.lo();
                UInt hi = e.hi();
                e = e.arg(0);
                idx = idx + lo;
                break;
            }

            case Z3_OP_BSHL: {
                ULong shift;
                if (e.arg(1).simplify().is_numeral_u64(shift)) {
                    if (idx < shift) {
                        return sbit_struct{ NULL, false, 0 };
                    }
                    else {
                        e = e.arg(0);
                        idx = idx - shift;
                    }
                    break;
                }
                goto ret;
            }
            case Z3_OP_BLSHR: {
                ULong shift;
                if (e.arg(1).simplify().is_numeral_u64(shift)) {
                    if ((size - idx) <= shift) {
                        return sbit_struct{ NULL, false, 0 };
                    }
                    else {
                        e = e.arg(0);
                        idx = idx + shift;
                    }
                    break;
                }
                goto ret;
            }
            case Z3_OP_BASHR: {
                ULong shift;
                if (e.arg(1).simplify().is_numeral_u64(shift)) {
                    e = e.arg(0);
                    if ((size - idx) <= shift) {
                        idx = size - 1;
                    }
                    else {
                        idx = idx + shift;
                    }
                    break;
                }
                goto ret;
            }
            case Z3_OP_CONCAT: {
                auto max = e.num_args();
                UInt shift = 0;

                for (Int i = max - 1; i >= 0; i--) {
                    z3::expr arg = e.arg(i);
                    z3::sort arg_s = arg.get_sort();
                    UInt arg_s_l = arg_s.bv_size();
                    if (idx >= shift && idx < (arg_s_l + shift)) {
                        e = arg;
                        idx = idx - shift;
                        break;
                    }
                    shift += arg_s_l;
                }
                break;
            }
            case Z3_OP_BXOR: {
                auto max = e.num_args();
                UInt n_sym = 0;
                sbit_struct rSS;
                bool rb = false;
                for (Int i = max - 1; i >= 0; i--) {
                    z3::expr arg = e.arg(i);
                    sbit_struct SS = _check_is_extract(arg, idx);
                    if (SS.sym_ast) {
                        n_sym += 1;
                        rSS = SS;
                        if (n_sym == 2) goto ret;
                    }
                    else {
                        rb ^= SS.rbit;
                    }
                }
                return n_sym ? rSS : sbit_struct{ NULL, rb , 0 };
            }
            case Z3_OP_BAND: {
                auto max = e.num_args();
                UInt n_sym = 0;
                sbit_struct rSS;
                for (Int i = max - 1; i >= 0; i--) {
                    z3::expr arg = e.arg(i);
                    sbit_struct SS = _check_is_extract(arg, idx);
                    if (SS.sym_ast) {
                        n_sym += 1;
                        rSS = SS;
                    }
                    else {
                        if (!SS.rbit)
                            return sbit_struct{ NULL, false , 0 };
                    }
                }
                if (n_sym == 1)
                    return rSS;
                if (n_sym == 0)
                    return sbit_struct{ NULL, true , 0 };
                goto ret;
            }

            case Z3_OP_BOR: {
                auto max = e.num_args();
                UInt n_sym = 0;
                sbit_struct rSS;
                for (Int i = max - 1; i >= 0; i--) {
                    z3::expr arg = e.arg(i);
                    sbit_struct SS = _check_is_extract(arg, idx);
                    if (SS.sym_ast) {
                        n_sym += 1;
                        rSS = SS;
                    }
                    else {
                        if (SS.rbit)
                            return sbit_struct{ NULL, true , 0 };
                    }
                }
                if (n_sym == 1)
                    return rSS;
                if (n_sym == 0)
                    return sbit_struct{ NULL, false , 0 };
                goto ret;
            }
            default:
                goto ret;
            };
        }
        else if (e.kind() == Z3_NUMERAL_AST) {
            ULong real;
            e.is_numeral_u64(real);
            return sbit_struct{ NULL, (bool)((real >> idx) & 1), 0 };
        }
        else {
            break;
        }
    }
ret:
    return sbit_struct{ e, false, idx };
}

template TR::addressingMode<Addr64>;
template TR::addressingMode<Addr32>;

