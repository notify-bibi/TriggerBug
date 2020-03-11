TR_add_include(z3_target_call src/engine/z3_target_call/ )
add_subdirectory(z3_target_call)
TR_add_library(TARGET libTriggerBug
               CONFIGURE_TYPE SHARED
               REQUIRE libz3 libvalgrind z3_target_call thread_pool)
TR_ADD_INCLUDE_DIRECTORIES(libTriggerBug z3_target_call)