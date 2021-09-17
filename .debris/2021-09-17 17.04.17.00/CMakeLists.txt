set(REMILL_INCLUDE_DIR "${CMAKE_SOURCE_DIR}/include")
add_subdirectory(BC)
target_include_directories(remill_bc PRIVATE ${LLVM_INCLUDE_DIRS} ${Z3_CXX_INCLUDE_DIRS})
set_target_properties(remill_bc PROPERTIES FOLDER "Utils")