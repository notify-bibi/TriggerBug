TR_add_library( TARGET TRtest 
                REQUIRE libtriggerBug libz3)
TR_ADD_INCLUDE_DIRECTORIES(TRtest libtriggerBug libz3 libvalgrind z3_target_call spdlog libvexllvm)
