# CMakeList.txt: TriggerBug 的 CMake 项目，在此处包括源代码并定义
# 项目特定的逻辑。
#
cmake_minimum_required (VERSION 3.9)

# 将源代码添加到此项目的可执行文件。
# add_compile_options(-std=c++17)
aux_source_directory(. DIR_TriggerBug_SRCS)
project(TriggerBug CXX)

INCLUDE_DIRECTORIES("functions/")
INCLUDE_DIRECTORIES("SimulationEngine/")
INCLUDE_DIRECTORIES("StateClass/")
INCLUDE_DIRECTORIES("Syscall/")
INCLUDE_DIRECTORIES("../Valgrind/priv/")
INCLUDE_DIRECTORIES("../Valgrind/pub/")
message("TriggerBug ${CMAKE_BINARY_DIR}")
message("TriggerBug ${CMAKE_SOURCE_DIR}")

add_library(TriggerBug SHARED ${DIR_TriggerBug_SRCS})

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

INCLUDE_DIRECTORIES(${TriggerBug_INCLUDE})

add_subdirectory ("./Z3_Target_Call")

TARGET_LINK_LIBRARIES(TriggerBug libz3 Valgrind Z3_Target_Call tinyxml2)

# TODO: 如有需要，请添加测试并安装目标。
