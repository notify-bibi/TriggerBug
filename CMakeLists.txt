# CMakeList.txt: 顶层 CMake 项目文件，在此处执行全局配置
# 并包含子项目。
#  λ cmake -G "Visual Studio 16 2019" -DDEBUG_GABLE=ON -DZ3_BUILD_LIBZ3_SHARED=ON -DZ3_USE_LIB_GMP=OFF -DZ3_SINGLE_THREADED=OFF -T ClangCL ..
#  rm -rf CMakeCache.txt CMakeFiles\

cmake_minimum_required (VERSION 3.8)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)


SET(DEBUG_GABLE OFF)
# -Gr __fastcall
# -Ot 代码速度优先
# -Oi inline内部函数
# -O3 优化速度
# /GS 安全检查
# /MD 多线程DLL库
# /Ob2 内联函数扩展 - 任何适用项 inline
# /Ob2  展开标记为 inline 或 __inline 的函数和编译器选择的任何其他函数（由编译器自行进行展开，通常称作自动内联）


set(EXTINSN -mmmx -msse -msse2 -msse3 -msse4.1 -msse4.2 -mssse3 -mavx -mavx2)

IF (WIN32)
	
	MESSAGE(STATUS "Now is windows")
	SET(CMAKE_C_FLAGS_RELEASE   "${CMAKE_C_FLAGS_RELEASE}   /utf-8 /Ob2 /Gr /Ot /Oi /O3 /GS- ")
	SET(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} /utf-8 /Ob2 /Gr /Ot /Oi /O3 /GS- ")
	add_definitions(/arch:AVX2)
	
else()
	SET(CMAKE_C_FLAGS_RELEASE   "${CMAKE_C_FLAGS_RELEASE}   -O3 -mavx -openmp -Qopenmp -Wall")
	SET(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3 -mavx -openmp -Qopenmp -Wall")

ENDIF ()
#  -fms-extensions open Microsoft extension (to support explicit constructor calls)
# https://clang.llvm.org/docs/UsersManual.html
add_compile_options(-fdeclspec 
					-fms-extensions -Wno-microsoft-explicit-constructor-call
					-fms-compatibility-version=19.00
					-fdiagnostics-show-template-tree
					-Wno-ambiguous-member-template
					-fimplicit-templates
					-Wno-extern-c-compat
					)
					

add_definitions(${EXTINSN})


project (TriggerBug
        VERSION 1.3.0
        DESCRIPTION "engine"
        LANGUAGES CXX
        )

SET(Z3_PROJ_DIR "z3-z3-4.8.9")
set(VALGRIND_PROJ_DIR "valgrind-3.16.1")
message(STATUS "TR version ${TriggerBug_VERSION} ")

if ("${PROJECT_SOURCE_DIR}" STREQUAL "${PROJECT_BINARY_DIR}")
  message(FATAL_ERROR "In source builds are not allowed. You should invoke "
          "CMake from a different directory.")
endif()

find_library(TR_PYTHON3_LIB_PATH python3 "${CMAKE_SOURCE_DIR}/lib")
IF(NOT TR_PYTHON3_LIB_PATH)
    MESSAGE(FATAL_ERROR "TriggerBug: /lib/python3.x dir not found")
ENDIF(NOT TR_PYTHON3_LIB_PATH) 
MESSAGE(STATUS ${TR_PYTHON3_LIB_PATH} " found")



# 加入一个配置头文件，用于处理 CMake 对源码的设置
# configure_file (
  # "${PROJECT_SOURCE_DIR}/config.h.in"
  # "${PROJECT_BINARY_DIR}/config.h"
  # )



include(cmake/tr_add_project.cmake)

set(CMAKE_INSTALL_LIBDIR ${CMAKE_BINARY_DIR}/lib)  
set(CMAKE_INSTALL_BINDIR ${CMAKE_BINARY_DIR}/bin) 
#set(CMAKE_INSTALL_INCLUDEDIR ${CMAKE_BINARY_DIR}/include) 
SET(CMAKE_INCLUDE_PATH ${CMAKE_SOURCE_DIR}/include/)

set(BUILD_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_INSTALL_BINDIR})
LINK_DIRECTORIES(${CMAKE_INSTALL_LIBDIR})
TR_add_include(libz3 ${Z3_PROJ_DIR}/ src src/api src/api/c++)
TR_add_include(libvalgrind ${VALGRIND_PROJ_DIR}/VEX/ priv/ pub/)
TR_add_include(libTriggerBug src/engine/ )
TR_add_include(thread_pool src/thread_pool)


option(BUILD_Z3 "BUILD Z3" OFF)
#option(BUILD_CFG "BUILD CFG" OFF)
option(BUILD_VALGRIND "BUILD VALGRIND" OFF)
option(BUILD_TRIGGERBUG "BUILD TRIGGERBUG" OFF)
option(BUILD_CRYPTO_ANALYZER "BUILD CRYPTO_ANALYZER" OFF)
option(BUILD_PYTHON_FRONTEND "BUILD PYTHON_BLACKEND" OFF)
option(BUILD_TRTEST "BUILD DEVELOP TEST" ON)


set(CMAKE_BINARY_DIR_tmp ${CMAKE_BINARY_DIR})
set(CMAKE_SOURCE_DIR_tmp ${CMAKE_SOURCE_DIR})

# ----------add lib z3----------
set(CMAKE_BINARY_DIR "${CMAKE_BINARY_DIR}/${Z3_PROJ_DIR}")
set(CMAKE_SOURCE_DIR "${CMAKE_SOURCE_DIR}/${Z3_PROJ_DIR}")

TR_lib_add(libz3 ${Z3_PROJ_DIR} BUILD_Z3 PATH ./lib)
IF (TARGET libz3)
    set_target_properties(libz3 PROPERTIES COMPILE_FLAGS "/openmp" )#yes
    set_target_properties(libz3 PROPERTIES COMPILE_FLAGS "/Qopenmp" )#yes
ENDIF()

set(CMAKE_BINARY_DIR ${CMAKE_BINARY_DIR_tmp})
set(CMAKE_SOURCE_DIR ${CMAKE_SOURCE_DIR_tmp})
unset(CMAKE_BINARY_DIR_tmp)
unset(CMAKE_SOURCE_DIR_tmp)

# ----------! lib z3 ----------

add_compile_options(-fdelayed-template-parsing)

add_subdirectory("src/thread_pool")
TR_lib_add(libvalgrind ${VALGRIND_PROJ_DIR}/VEX/ BUILD_VALGRIND)
TR_lib_add(libTriggerBug "src/engine" BUILD_TRIGGERBUG)
TR_lib_add(libcrypto_analyzer "src/crypto_analyzer" BUILD_CRYPTO_ANALYZER)
TR_lib_add(libpythonfront "src/python" BUILD_PYTHON_FRONTEND)
TR_lib_add(TRtest "src/test" BUILD_TRTEST)
#TR_lib_add(libcfg "src/CFG" BUILD_CFG)


