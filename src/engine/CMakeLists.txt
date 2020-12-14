TR_add_include(vexTargetCall src/engine/z3_target_call/ )
add_subdirectory(z3_target_call)
TR_add_library(TARGET libtriggerBug
               CONFIGURE_TYPE SHARED
               REQUIRE libz3 libvalgrind vexTargetCall threadPool)
TR_ADD_INCLUDE_DIRECTORIES(libtriggerBug vexTargetCall)