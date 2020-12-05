
TR_add_library( TARGET libpythonfront
                CONFIGURE_TYPE SHARED
                REQUIRE libTriggerBug python3)
TR_ADD_INCLUDE_DIRECTORIES(libpythonfront libz3 libvalgrind z3_target_call)
