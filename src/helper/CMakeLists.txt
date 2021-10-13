
add_compile_options(-Wno-unused-variable)
TR_add_library(TARGET vexcallhelper 
               CONFIGURE_TYPE STATIC
               SOURCES 
                    "z3_target_call.cxx"
                    "AMD64/amd64CCall.cxx"
                    "X86/x86_CCall.cxx"
                    )


target_link_libraries(vexcallhelper PUBLIC libvalgrind z3::libz3)

set_target_properties(vexcallhelper PROPERTIES FOLDER "Core")