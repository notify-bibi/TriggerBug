
find_library(TR_PYTHON3_LIB_PATH python3 "${CMAKE_SOURCE_DIR}/lib")
IF(NOT TR_PYTHON3_LIB_PATH)
    MESSAGE(FATAL_ERROR "TriggerBug: /lib/python3.x dir not found")
ENDIF(NOT TR_PYTHON3_LIB_PATH) 
MESSAGE(STATUS ${TR_PYTHON3_LIB_PATH} " found")

TR_add_library( TARGET libpythonfront
                CONFIGURE_TYPE SHARED
                REQUIRE libTriggerBug python3)
TR_ADD_INCLUDE_DIRECTORIES(libpythonfront libz3 libvalgrind z3_target_call tinyxml2)
