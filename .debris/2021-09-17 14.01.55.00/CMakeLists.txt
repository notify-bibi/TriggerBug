
TR_add_library(TARGET libtriggerBug
               CONFIGURE_TYPE SHARED
               REQUIRE libz3 libvalgrind vexTargetCall threadPool spdlog
               )
			   
			   
#target_include_directories(libtriggerBug PUBLIC ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(libtriggerBug PUBLIC libvalgrind z3::libz3 spdlog::spdlog)
# TR_ADD_INCLUDE_DIRECTORIES(libtriggerBug vexTargetCall)