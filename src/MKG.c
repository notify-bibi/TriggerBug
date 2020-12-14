/*clang-cl.exe -E MKG.c 1>> xx.txt*/

#include "libvex.h"

#define GEN_MKG 

#define MKG_AMD64
#define MKG_X86
#define MKG_ARM
#define MKG_ARM64
#define MKG_MIPS
#define MKG_NANOMIPS
#define MKG_PPC

#define MKG_VAR_CALL(NAME_SPACE, TYPE, VAR) TYPE (*NAME_SPACE##_##VAR##_var_call());    


#include "config.h"



#define MKG_VAR_CALL(NAME_SPACE, TYPE, VAR)             \
TYPE* NAME_SPACE##_##VAR##_var_call(){ static thread_local TYPE VAR; return &VAR; }                  \



#include "config.h"