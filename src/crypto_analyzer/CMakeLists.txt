TR_add_library( TARGET libcryptoAnalyzer
                CONFIGURE_TYPE SHARED 
                )
                
                
target_link_libraries(libcryptoAnalyzer PUBLIC z3::libz3 libengine)
set_target_properties(libcryptoAnalyzer PROPERTIES FOLDER "Loadable modules")