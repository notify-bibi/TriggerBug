TR_add_library( TARGET libcrypto_analyzer 
                CONFIGURE_TYPE SHARED 
                REQUIRE libTriggerBug)
                

TR_ADD_INCLUDE_DIRECTORIES(libcrypto_analyzer libz3 libvalgrind z3_target_call)