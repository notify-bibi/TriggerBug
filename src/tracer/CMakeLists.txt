TR_add_library(TARGET obj.instoptGraphWriter
               CONFIGURE_TYPE STATIC
               )
			   
			   
target_link_libraries(obj.instoptGraphWriter PUBLIC libengine libvexllvm)
set_target_properties(obj.instoptGraphWriter PROPERTIES FOLDER "Object Libraries")
