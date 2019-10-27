# CMakeList.txt: TriggerBug 的 CMake 项目，在此处包括源代码并定义
# 项目特定的逻辑。
#
cmake_minimum_required (VERSION 3.9)

# 将源代码添加到此项目的可执行文件。
# add_compile_options(-std=c++17)
# aux_source_directory(. DIR_TriggerBug_SRCS)
project(TriggerBug CXX)

add_subdirectory ("./SimulationEngine")

INCLUDE_DIRECTORIES("functions/")
INCLUDE_DIRECTORIES("SimulationEngine/")
INCLUDE_DIRECTORIES("Syscall/")
INCLUDE_DIRECTORIES("../Valgrind/priv/")
INCLUDE_DIRECTORIES("../Valgrind/pub/")
INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src")
message("TriggerBug ${CMAKE_BINARY_DIR}")
message("TriggerBug ${CMAKE_SOURCE_DIR}")

add_library(TriggerBug SHARED "TriggerBug.cpp")
add_library(libPyInterFace SHARED "libPyInterFace.cpp")

SET(TriggerBug_INCLUDE ${CMAKE_SOURCE_DIR}/include/)

message(STATUS "TriggerBug_INCLUDE: ${TriggerBug_INCLUDE}")

INCLUDE_DIRECTORIES("${TriggerBug_INCLUDE}")
INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src/z3/src/api")
INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src/z3/src/api/c++")


find_library(LIB_PATH python3 "${CMAKE_SOURCE_DIR}/lib")
IF(NOT LIB_PATH)
MESSAGE(FATAL_ERROR "TriggerBug: /lib/python3.lib dir not found")
ENDIF(NOT LIB_PATH) 

MESSAGE(STATUS ${LIB_PATH} " found")
TARGET_LINK_LIBRARIES(TriggerBug ${LIB_PATH})
TARGET_LINK_LIBRARIES(libPyInterFace ${LIB_PATH})

INCLUDE_DIRECTORIES(${TriggerBug_INCLUDE})


TARGET_LINK_LIBRARIES(TriggerBug SimulationEngine libz3 Valgrind tinyxml2)
set_target_properties(TriggerBug PROPERTIES COMPILE_FLAGS "/openmp" )#yes
set_target_properties(TriggerBug PROPERTIES COMPILE_FLAGS "/Qopenmp" )#yes


TARGET_LINK_LIBRARIES(libPyInterFace SimulationEngine libz3 Valgrind tinyxml2)
set_target_properties(libPyInterFace PROPERTIES COMPILE_FLAGS "/openmp" )#yes
set_target_properties(libPyInterFace PROPERTIES COMPILE_FLAGS "/Qopenmp" )#yes
# TODO: 如有需要，请添加测试并安装目标。
