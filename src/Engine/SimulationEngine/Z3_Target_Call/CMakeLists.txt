# CMakeList.txt: Z3_Target_Call 的 CMake 项目，在此处包括源代码并定义
# 项目特定的逻辑。
#
cmake_minimum_required (VERSION 3.9)

# 将源代码添加到此项目的可执行文件。
# add_compile_options(-std=c++17)
aux_source_directory(. DIR_Z3_Target_Call_SRCS)
project(Z3_Target_Call CXX)
add_library(Z3_Target_Call "Z3_Target_Call.cpp")
INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src/z3/src/api")
INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src/z3/src/api/c++")


TARGET_LINK_LIBRARIES(Z3_Target_Call)

# TODO: 如有需要，请添加测试并安装目标。
