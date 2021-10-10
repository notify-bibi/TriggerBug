TR_add_library( TARGET InstoptUtils 
                CONFIGURE_TYPE STATIC 
              )
              
llvm_map_components_to_libnames(llvm_libs support core irreader bitwriter)
target_link_libraries(InstoptUtils LINK_PRIVATE
  ${llvm_libs} glog::glog gflags
)

set_target_properties(InstoptUtils PROPERTIES FOLDER "Utils")