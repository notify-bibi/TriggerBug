include_directories(${LLVM_INCLUDE_DIRS} ${Z3_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

TR_add_library( TARGET TRtest 
                REQUIRE libtriggerBug libz3 libvexllvm)
target_link_libraries(TRtest PRIVATE libtriggerBug libvexllvm remill_bc remill_os helper)
# TR_ADD_INCLUDE_DIRECTORIES(TRtest libtriggerBug libz3 libvalgrind z3_target_call spdlog libvexllvm)

set_target_properties(TRtest PROPERTIES FOLDER "Tests")