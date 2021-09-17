set(REMILL_INCLUDE_DIR "${CMAKE_SOURCE_DIR}/include")
add_subdirectory(BC)
set_target_properties(remill_bc PROPERTIES FOLDER "Utils")