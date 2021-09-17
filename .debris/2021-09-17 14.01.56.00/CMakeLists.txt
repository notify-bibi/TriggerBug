
add_compile_options(-Wno-unused-variable)
TR_add_library(TARGET helper 
               CONFIGURE_TYPE STATIC
               SOURCES 
                    "z3_target_call.cxx"
                    "AMD64/amd64CCall.cxx"
                    "X86/x86_CCall.cxx"
                    )
target_include_directories(helper PUBLIC ${Z3_CXX_INCLUDE_DIRS})
# TR_ADD_INCLUDE_DIRECTORIES(helper libz3 libvalgrind)
