TR_add_library(TARGET z3_target_call 
               CONFIGURE_TYPE STATIC
               SOURCES 
                    "z3_target_call.cxx"
                    "AMD64/amd64CCall.cxx"
                    "X86/x86_CCall.cxx"
                    )
TR_ADD_INCLUDE_DIRECTORIES(z3_target_call libz3 libvalgrind)
