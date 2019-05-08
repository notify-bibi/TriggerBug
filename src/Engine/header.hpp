#ifndef HEADER_H
#define HEADER_H
#define Z3_Get_Ref(exp) (((int*)((Z3_ast)((exp))))[2])


#define TESTCODE(code)																								    	 \
{																															 \
	LARGE_INTEGER   freq = { 0 };																							 \
	LARGE_INTEGER   beginPerformanceCount = { 0 };																			 \
	LARGE_INTEGER   closePerformanceCount = { 0 };																			 \
	QueryPerformanceFrequency(&freq);																						 \
	QueryPerformanceCounter(&beginPerformanceCount);																		 \
	{code	}																												 \
	QueryPerformanceCounter(&closePerformanceCount);																		 \
	double delta_seconds = (double)(closePerformanceCount.QuadPart - beginPerformanceCount.QuadPart) / freq.QuadPart;		 \
	printf("%s line:%d spend %lf \n",__FILE__, __LINE__, delta_seconds);													 \
}



#define TransLate(toctx,ctx,_ast) to_expr(toctx, Z3_translate(ctx, _ast, toctx))
#define ALIGN(Value,size) ((Value) & ~((size) - 1))

extern "C" 
{
#include "../Valgrind/pub/libvex.h";
}
extern "C" Bool vex_initdone;
extern "C" unsigned char tid2temp[0x10000];
extern "C" tid_type register_tid(unsigned int);
extern "C" tid_type unregister_tid(unsigned int);
extern "C" void tempmeminit();
extern "C" void init_threads_id();
extern "C" void vex_assert_fail(const HChar* expr,const HChar* file, Int line, const HChar* fn);
extern "C" unsigned int vex_printf(const HChar* format, ...);
extern "C" void vpanic(const HChar* str);

static unsigned char fastalignD1[257 ];
static unsigned char fastalign[257];
static ULong fastMask[65];
static ULong fastMaskI1[65];
static ULong fastMaskB[9];
static ULong fastMaskBI1[9];

static ULong fastMaskReverse[65];
static ULong fastMaskReverseI1[65];


class State;
class Variable;

typedef struct ChangeView {
	State *elders;
	ChangeView *front;
}ChangeView;

typedef enum :unsigned int {
	NewState = 0,
	Running,
	Fork,
	Death
}State_Tag;



class State;
typedef State_Tag(*CallBack)(State *);
typedef struct _Hook {
	CallBack cb;
	UChar original;
}Hook_struct;





#define SetRecord(record,offset,length) {((record))[((offset)>>5)]=True;if((length)!=1) {((record))[((offset)+(length)-1)>>5]=True;}}



#ifdef _DEBUG

#define vassert(expr)                                           \
  ((void) ((expr) ? 0 :											\
           (vex_assert_fail (#expr,                             \
                             __FILE__, __LINE__,                \
                             __FUNCSIG__), 0)))
#else
#define vassert(...) 
#endif // _DEBUG






/* vex_traceflags values */
#define VEX_TRACE_FE     (1 << 7)  /* show conversion into IR */
#define VEX_TRACE_OPT1   (1 << 6)  /* show after initial opt */
#define VEX_TRACE_INST   (1 << 5)  /* show after instrumentation */
#define VEX_TRACE_OPT2   (1 << 4)  /* show after second opt */
#define VEX_TRACE_TREES  (1 << 3)  /* show after tree building */
#define VEX_TRACE_VCODE  (1 << 2)  /* show selected insns */
#define VEX_TRACE_RCODE  (1 << 1)  /* show after reg-alloc */
#define VEX_TRACE_ASM    (1 << 0)  /* show final assembly */


#define SET1(addr, value) *(UChar*)((addr)) = (value)
#define SET2(addr, value) *(UShort*)((addr)) = (value)
#define SET4(addr, value) *(UInt*)((addr)) = (value)
#define SET8(addr, value) *(ULong*)((addr)) = (value)
#define SET16(addr, value) *(__m128i*)((addr)) = (value)
#define SET32(addr, value) *(__m256i*)((addr)) = (value)

#define GET1(addr) (*(UChar*)((addr))) 
#define GET2(addr) (*(UShort*)((addr)))
#define GET4(addr) (*(UInt*)((addr)))
#define GET8(addr) (*(ULong*)((addr)))
#define GET16(addr) (*(__m128i*)((addr)))
#define GET32(addr) (*(__m256i*)((addr)))


#define GETS1(addr) (*(Char*)((addr))) 
#define GETS2(addr) (*(Short*)((addr)))
#define GETS4(addr) (*(Int*)((addr)))
#define GETS8(addr) (*(Long*)((addr)))
#define GETS16(addr) (*(__m128i*)((addr)))
#define GETS32(addr) (*(__m256i*)((addr)))

#define MV1(addr,fromaddr) *(UChar*)((addr))=(*(UChar*)((fromaddr))) 
#define MV2(addr,fromaddr) *(UShort*)((addr))=(*(UShort*)((fromaddr)))
#define MV4(addr,fromaddr) *(UInt*)((addr))=(*(UInt*)((fromaddr)))
#define MV8(addr,fromaddr) *(ULong*)((addr))=(*(ULong*)((fromaddr)))
#define MV16(addr,fromaddr) *(__m128i*)((addr))=(*(__m128i*)((fromaddr)))
#define MV32(addr,fromaddr) *(__m256i*)((addr))=(*(__m256i*)((fromaddr)))

typedef enum:unsigned char {
	e_nothing,
	e_symbolic,
	e_real
}memTAG;

#define SETFAST(fast_ptr,__nbytes) \
if((__nbytes)<8){\
__asm__(\
	"mov %[nbytes],%%cl;\n\t"\
	"shl $3,%%rcx;\n\t"\
	"mov %[fast],%%rax;\n\t"\
	"shr %%cl,%%rax;\n\t"\
	"shl %%cl,%%rax;\n\t"\
	"mov $0x0807060504030201,%%rbx;\n\t"\
	"sub $65,%%cl;\n\t"\
	"not %%cl;\n\t"\
	"shl %%cl,%%rbx;\n\t"\
	"shr %%cl,%%rbx;\n\t"\
	"or %%rbx,%%rax;\n\t"\
	"mov %%rax,%[out];\n\t"\
	: [out]"=r"(GET8((fast_ptr)))\
	: [fast] "r"(GET8((fast_ptr))), [nbytes] "r"((UChar)(__nbytes))\
	: "rax", "rbx", "rcx"\
);}										\
else if((__nbytes)==8){					\
	SET8((fast_ptr),0x0807060504030201);\
}else{									\
	for(UChar _i=0;_i<(__nbytes);_i++){	\
		(fast_ptr)[_i]=_i+1;			\
	}									\
}										



#define Z3SETBYTES(bytes_ptr,__nbit,z3_re_u64) \
if((__nbit)==64){ SET8((bytes_ptr),z3_re_u64);}\
else{\
__asm__(\
	"mov %[nb],%%cl;\n\t"\
	"mov %[fast],%%rax;\n\t"\
	"shr %%cl,%%rax;\n\t"\
	"shl %%cl,%%rax;\n\t"\
	"mov %[int64],%%rbx;\n\t"\
	"sub $65,%%cl;\n\t"\
	"not %%cl;\n\t"\
	"shl %%cl,%%rbx;\n\t"\
	"shr %%cl,%%rbx;\n\t"\
	"or %%rbx,%%rax;\n\t"\
	"mov %%rax,%[out];\n\t"\
	: [out]"=r"(GET8((bytes_ptr)))\
	: [fast] "r"(GET8((bytes_ptr))), [nb] "r"((UChar)(__nbit)),[int64] "r"((z3_re_u64)) \
	: "rax", "rbx", "rcx"\
);}


#define vpanic(...) printf("%s line %d",__FILE__,__LINE__); vpanic(__VA_ARGS__);

static std::mutex global_user_mutex;
static UInt global_user = 0;
static UInt newDifUser()
{
	{
		std::unique_lock<std::mutex> lock(global_user_mutex);
		return global_user++;
	}
}

extern std::string replace(const char *pszSrc, const char *pszOld, const char *pszNew);
extern unsigned int eval_all(std::vector<Z3_ast> &result, z3::solver &solv, Z3_ast nia);
extern LARGE_INTEGER   freq_global;
extern LARGE_INTEGER   beginPerformanceCount_global;
extern LARGE_INTEGER   closePerformanceCount_global;
extern VexArch guest;

#endif // HEADER_H

