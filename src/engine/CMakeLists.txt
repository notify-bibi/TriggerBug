
TR_add_library(TARGET libengine
               CONFIGURE_TYPE SHARED
               REQUIRE libz3 libvalgrind vexTargetCall InstoptUtils spdlog
               )
			   
			   
target_include_directories(libengine PUBLIC ${Z3_INCLUDE_DIRS})
target_link_libraries(libengine PUBLIC libvalgrind z3::libz3 spdlog::spdlog InstoptUtils)
target_link_libraries(libengine PRIVATE vexcallhelper)
# TR_ADD_INCLUDE_DIRECTORIES(libengine vexTargetCall)


set_target_properties(libengine PROPERTIES FOLDER "Core")

if (CMAKE_SYSTEM_NAME MATCHES "[Ww]indows")
  # On Windows we need to copy the Z3 libraries
  # into the same directory as the executable
  # so that they can be found.
  foreach (z3_lib ${Z3_LIBRARIES})
    message(STATUS "Adding copy rule for ${z3_lib}")
    add_custom_command(TARGET libengine
      POST_BUILD
      COMMAND
        ${CMAKE_COMMAND} -E copy_if_different
        $<TARGET_FILE:${z3_lib}>
        $<TARGET_FILE_DIR:libengine>
    )
  endforeach()
endif()