set(REMILL_INCLUDE_DIR "${CMAKE_SOURCE_DIR}/include")
add_subdirectory(BC)
target_link_libraries(libvexllvm PUBLIC ${llvm_libs})
set_target_properties(remill_bc PROPERTIES FOLDER "Utils")