
TR_add_library( TARGET libpythonFront
                CONFIGURE_TYPE SHARED
                REQUIRE libtriggerBug python3)
TR_ADD_INCLUDE_DIRECTORIES(libpythonFront libz3 libvalgrind z3_target_call)
