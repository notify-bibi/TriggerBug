include_directories(${LLVM_INCLUDE_DIRS} ${Z3_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

TR_add_library( TARGET test-cfg )
target_link_libraries(test-cfg  PRIVATE libtriggerBug libvexllvm helper libGraphWriter)
set_target_properties(test-cfg  PROPERTIES FOLDER "Tests")