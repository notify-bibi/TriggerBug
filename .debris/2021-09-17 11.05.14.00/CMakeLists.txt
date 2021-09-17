
TR_add_library(TARGET libtriggerBug
               CONFIGURE_TYPE SHARED
               REQUIRE libz3 libvalgrind vexTargetCall threadPool spdlog
               )
			   
			   
target_include_directories(libtriggerBug PUBLIC ${Z3_CXX_INCLUDE_DIRS})
# TR_ADD_INCLUDE_DIRECTORIES(libtriggerBug vexTargetCall)