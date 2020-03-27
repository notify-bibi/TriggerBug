

// https://software.intel.com/sites/landingpage/IntrinsicsGuide/#expand=0,27,1022,79,115,5771,2476,73,72,6141,1148,1015,1148,915,891,891,4993&techs=MMX,SSE,SSE2,SSE3,SSSE3,SSE4_1,SSE4_2,AVX,AVX2,FMA,AVX_512,KNC,SVML&text=_mm256_setr_epi64x


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


#define atos(n) ((sbval<n>&)a)
#define atou(n) ((ubval<n>&)a)
#define btos(n) ((sbval<n>&)b)
#define btou(n) ((ubval<n>&)b)
#define ctos(n) ((sbval<n>&)c)
#define ctou(n) ((ubval<n>&)c)
#define dtos(n) ((sbval<n>&)d)
#define dtou(n) ((ubval<n>&)d)



#define ato(t) ((sv::ctype_val<t>&)a)
#define bto(t) ((sv::ctype_val<t>&)b)
#define cto(t) ((sv::ctype_val<t>&)c)
#define dto(t) ((sv::ctype_val<t>&)a)