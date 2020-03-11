#include "compress.h"

using namespace cmpr;

thread_local Z3_context thread_z3_ctx;
Z3_context& thread_get_z3_ctx() {
    return thread_z3_ctx; 
}