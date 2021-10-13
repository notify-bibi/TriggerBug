include_directories(${LLVM_INCLUDE_DIRS})
include_directories(${Z3_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

TR_add_library( TARGET test-core )
target_link_libraries(test-core PRIVATE libengine libvexllvm vexcallhelper)
set_target_properties(test-core PROPERTIES FOLDER "Tests")