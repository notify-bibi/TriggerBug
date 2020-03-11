
#include "engine/kernel.h"
#include <mmintrin.h>  //MMX
#include <xmmintrin.h> //SSE(include mmintrin.h)
#include <emmintrin.h> //SSE2(include xmmintrin.h)
#include <pmmintrin.h> //SSE3(include emmintrin.h)
#include <tmmintrin.h> //SSSE3(include pmmintrin.h)
#include <smmintrin.h> //SSE4.1(include tmmintrin.h)
#include <nmmintrin.h> //SSE4.2(include smmintrin.h)
#include <wmmintrin.h> //AES(include nmmintrin.h)
#include <immintrin.h> //AVX(include wmmintrin.h)
#include <intrin.h>    //(include immintrin.h)
#include <dvec.h>

using namespace z3;

static inline Z3_ast bool2bv(Z3_context ctx, Z3_ast ast) {
    Z3_inc_ref(ctx, ast);
    Z3_sort sort = Z3_mk_bv_sort(ctx, 1);
    Z3_inc_ref(ctx, (Z3_ast)sort);
    Z3_ast zero = Z3_mk_int(ctx, 0, sort);
    Z3_inc_ref(ctx, zero);
    Z3_ast one = Z3_mk_int(ctx, 1, sort);
    Z3_inc_ref(ctx, one);
    Z3_ast result = Z3_mk_ite(ctx, ast, one, zero);
    Z3_dec_ref(ctx, one);
    Z3_dec_ref(ctx, zero);
    Z3_dec_ref(ctx, ast);
    Z3_dec_ref(ctx, (Z3_ast)sort);
    return result;
}
