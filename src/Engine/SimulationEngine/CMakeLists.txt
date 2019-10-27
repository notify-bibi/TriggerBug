# CMakeList.txt: TriggerBug 的 CMake 项目，在此处包括源代码并定义
# 项目特定的逻辑。
#
cmake_minimum_required (VERSION 3.9)

# 将源代码添加到此项目的可执行文件。
# add_compile_options(-std=c++17)
aux_source_directory(. DIR_SimulationEngine_SRCS)
project(SimulationEngine CXX)

INCLUDE_DIRECTORIES("functions/")
INCLUDE_DIRECTORIES("SimulationEngine/")
INCLUDE_DIRECTORIES("Syscall/")
INCLUDE_DIRECTORIES("../../Valgrind/priv/")
INCLUDE_DIRECTORIES("../../Valgrind/pub/")
INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src")
INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src/z3/src/api")
INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src/z3/src/api/c++")
SET(TriggerBug_INCLUDE ${CMAKE_SOURCE_DIR}/include/)
INCLUDE_DIRECTORIES("${TriggerBug_INCLUDE}")

add_subdirectory ("./Z3_Target_Call")
add_library(SimulationEngine "State_class.cpp" "memory.cpp" "Register.cpp")


TARGET_LINK_LIBRARIES(SimulationEngine Z3_Target_Call)
set_target_properties(SimulationEngine PROPERTIES COMPILE_FLAGS "/openmp" )#yes
set_target_properties(SimulationEngine PROPERTIES COMPILE_FLAGS "/Qopenmp" )#yes
# TODO: 如有需要，请添加测试并安装目标。
