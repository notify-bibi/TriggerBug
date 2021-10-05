include_directories(${LLVM_INCLUDE_DIRS} ${Z3_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

TR_add_library( TARGET test-core )
target_link_libraries(test-core  PRIVATE libtriggerBug libvexllvm remill_bc remill_os helper)
set_target_properties(test-core  PROPERTIES FOLDER "Tests")