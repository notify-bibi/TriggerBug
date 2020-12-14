TR_add_library(TARGET vexTargetCall 
               CONFIGURE_TYPE STATIC
               SOURCES 
                    "z3_target_call.cxx"
                    "AMD64/amd64CCall.cxx"
                    "X86/x86_CCall.cxx"
                    )
TR_ADD_INCLUDE_DIRECTORIES(vexTargetCall libz3 libvalgrind)
