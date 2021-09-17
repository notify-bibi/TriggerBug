TR_add_library( TARGET libcryptoAnalyzer
                CONFIGURE_TYPE SHARED 
                REQUIRE libtriggerBug)
                
                
target_link_libraries(libcryptoAnalyzer PUBLIC libz3)

# TR_ADD_INCLUDE_DIRECTORIES(libcryptoAnalyzer libz3 libvalgrind z3_target_call)