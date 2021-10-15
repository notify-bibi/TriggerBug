# include_directories(${Z3_INCLUDE_DIRS})
TR_add_library( TARGET test-z3 )
target_link_libraries(test-z3  PRIVATE z3::libz3)
set_target_properties(test-z3  PROPERTIES FOLDER "Tests")

if (CMAKE_SYSTEM_NAME MATCHES "[Ww]indows")
  # On Windows we need to copy the Z3 libraries
  # into the same directory as the executable
  # so that they can be found.
  foreach (z3_lib ${Z3_LIBRARIES})
    message(STATUS "Adding copy rule for ${test-z3}")
    add_custom_command(TARGET test-z3
      POST_BUILD
      COMMAND
        ${CMAKE_COMMAND} -E copy_if_different
        $<TARGET_FILE:${z3_lib}>
        $<TARGET_FILE_DIR:test-z3>
    )
  endforeach()
endif()