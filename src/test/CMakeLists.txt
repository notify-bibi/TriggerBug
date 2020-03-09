TR_add_library( TARGET TRtest 
                REQUIRE libTriggerBug libz3 tinyxml2)
TR_ADD_INCLUDE_DIRECTORIES(TRtest libTriggerBug libz3 libvalgrind z3_target_call tinyxml2)
