
add_compile_options(-Wno-unused-variable)
TR_add_library(TARGET obj.instoptVexHelper 
               CONFIGURE_TYPE STATIC
               SOURCES 
                    "z3_target_call.cxx"
                    "AMD64/amd64CCall.cxx"
                    "X86/x86_CCall.cxx"
                    )


target_link_libraries(obj.instoptVexHelper PUBLIC libvalgrind z3::libz3)

set_target_properties(obj.instoptVexHelper PROPERTIES FOLDER "Object Libraries")
