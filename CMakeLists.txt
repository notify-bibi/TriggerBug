# CMakeList.txt: 顶层 CMake 项目文件，在此处执行全局配置
# 并包含子项目。
#
cmake_minimum_required (VERSION 3.9)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

project ("TriggerBug")

# 包含子项目。
ADD_DEFINITIONS(-D __x86_64__)
ADD_DEFINITIONS(-D VGA_x86)
ADD_DEFINITIONS(-D VGA_amd64)
ADD_DEFINITIONS(-D VGA_ppc32)
ADD_DEFINITIONS(-D VGA_ppc64be)
ADD_DEFINITIONS(-D VGA_arm)
ADD_DEFINITIONS(-D VGA_arm64)	 
ADD_DEFINITIONS(-D VGA_mips32) 
ADD_DEFINITIONS(-D VGA_mips64) 
#ADD_DEFINITIONS(-D VGA_s390x)
aux_source_directory(. DIRSRCS)
add_subdirectory ("./src/Valgrind")
add_subdirectory ("./src/z3")
add_subdirectory ("./src/Engine")
add_subdirectory ("./src/tinyxml2")
#add_subdirectory ("./src/CFG")

LINK_DIRECTORIES("./lib")