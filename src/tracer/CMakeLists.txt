TR_add_library(TARGET libGraphWriter
               CONFIGURE_TYPE STATIC
               )
			   
			   
target_link_libraries(libGraphWriter PUBLIC libengine libvexllvm)
set_target_properties(libGraphWriter PROPERTIES FOLDER "Tracer")
