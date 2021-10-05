include_directories(${LLVM_INCLUDE_DIRS} ${Z3_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

TR_add_library( TARGET test-cfg )
target_link_libraries(test-cfg  PRIVATE libtriggerBug libvexllvm remill_settings remill_bc remill_arch remill_os helper libGraphWriter)
set_target_properties(test-cfg  PROPERTIES FOLDER "Tests")