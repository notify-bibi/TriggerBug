# CMakeList.txt: 顶层 CMake 项目文件，在此处执行全局配置
# 并包含子项目。
#
cmake_minimum_required (VERSION 3.9.9)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

SET(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3 -Ob2 /Qopenmp -Wall")
SET(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -O3 -Ob2  -Wall")
add_compile_options("$<$<CONFIG:RELEASE>:-std=c++17 -O3 -Ob2 /Qopenmp /GS->")

project (TriggerBug
        VERSION 1.3.0
        DESCRIPTION "engine"
        LANGUAGES CXX
        )


message(STATUS "TR version ${TriggerBug_VERSION} ")

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

include(cmake/tr_add_project.cmake)


set(CMAKE_INSTALL_LIBDIR ${CMAKE_SOURCE_DIR}/lib)  
set(CMAKE_INSTALL_BINDIR ${CMAKE_SOURCE_DIR}/bin) 
set(BUILD_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_INSTALL_BINDIR})
SET(CMAKE_INCLUDE_PATH ${CMAKE_SOURCE_DIR}/include/)
LINK_DIRECTORIES(${CMAKE_INSTALL_LIBDIR})
TR_add_include(libz3 z3/ src src/api src/api/c++)
TR_add_include(libvalgrind src/valgrind/ priv/ pub/)
TR_add_include(libTriggerBug src/engine/ )
TR_add_include(thread_pool src/thread_pool)

option(BUILD_Z3 "BUILD Z3" OFF)
#option(BUILD_CFG "BUILD CFG" OFF)
option(BUILD_VALGRIND "BUILD VALGRIND" OFF)
option(BUILD_TRIGGERBUG "BUILD TRIGGERBUG" OFF)
option(BUILD_CRYPTO_ANALYZER "BUILD CRYPTO_ANALYZER" OFF)
option(BUILD_PYTHON_FRONTEND "BUILD PYTHON_BLACKEND" OFF)
option(BUILD_TRTEST "BUILD DEVELOP TEST" ON)

add_subdirectory("src/thread_pool")

set(CMAKE_BINARY_DIR_tmp ${CMAKE_BINARY_DIR})
set(CMAKE_SOURCE_DIR_tmp ${CMAKE_SOURCE_DIR})

# ----------add lib z3----------
set(CMAKE_BINARY_DIR "${CMAKE_BINARY_DIR}/z3")
set(CMAKE_SOURCE_DIR "${CMAKE_SOURCE_DIR}/z3")

TR_lib_add(libz3 "z3" BUILD_Z3 PATH ./lib)
IF (TARGET libz3)
    set_target_properties(libz3 PROPERTIES COMPILE_FLAGS "/openmp" )#yes
    set_target_properties(libz3 PROPERTIES COMPILE_FLAGS "/Qopenmp" )#yes
ENDIF()

set(CMAKE_BINARY_DIR ${CMAKE_BINARY_DIR_tmp})
set(CMAKE_SOURCE_DIR ${CMAKE_SOURCE_DIR_tmp})
unset(CMAKE_BINARY_DIR_tmp)
unset(CMAKE_SOURCE_DIR_tmp)

# ----------! lib z3 ----------

TR_lib_add(libvalgrind "src/valgrind" BUILD_VALGRIND)
TR_lib_add(libTriggerBug "src/engine" BUILD_TRIGGERBUG)
TR_lib_add(libcrypto_analyzer "src/crypto_analyzer" BUILD_CRYPTO_ANALYZER)
TR_lib_add(libpythonfront "src/python" BUILD_PYTHON_FRONTEND)
TR_lib_add(TRtest "src/test" BUILD_TRTEST)
#TR_lib_add(libcfg "src/CFG" BUILD_CFG)

