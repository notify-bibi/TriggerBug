


# Set your project compile flags.
# E.g. if using the C++ header files
# you will need to enable C++11 support
# for your compiler.
llvm_map_components_to_libnames(llvm_libs support core irreader bitwriter)


TR_add_library( TARGET libvexllvm 
                CONFIGURE_TYPE SHARED
              )

# target_include_directories(libvexllvm PRIVATE ${LLVM_INCLUDE_DIRS} ${Z3_CXX_INCLUDE_DIRS})
target_compile_definitions(libvexllvm PRIVATE -DVEXLLVM_HELPER_PATH="${CMAKE_SOURCE_DIR}/bitcode")
target_link_libraries(libvexllvm PUBLIC ${llvm_libs})
target_link_libraries(libvexllvm PRIVATE glog::glog  gflags_shared)
set_target_properties(libvexllvm PROPERTIES FOLDER "Core")