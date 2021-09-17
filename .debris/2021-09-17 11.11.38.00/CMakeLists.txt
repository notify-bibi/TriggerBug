TR_add_library( TARGET libcryptoAnalyzer
                CONFIGURE_TYPE SHARED 
                REQUIRE libtriggerBug)
                
                
target_include_directories(libcryptoAnalyzer PRIVATE ${CMAKE_CURRENT_LIST_DIR}/priv)
target_include_directories(libcryptoAnalyzer PUBLIC ${CMAKE_CURRENT_LIST_DIR}/pub)
target_link_libraries(libcryptoAnalyzer PUBLIC libz3)

# TR_ADD_INCLUDE_DIRECTORIES(libcryptoAnalyzer libz3 libvalgrind z3_target_call)