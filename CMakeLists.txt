# CMakeList.txt: 顶层 CMake 项目文件，在此处执行全局配置
# 并包含子项目。


# VMWIN
# λ wget https://github.com/llvm/llvm-project/releases/download/llvmorg-12.0.1/llvm-12.0.1.src.tar.xz
# λ cmake -G "Visual Studio 16 2019" -A x64 -T ClangCL -DCMAKE_BUILD_TYPE=Release -DLLVM_BUILD_TOOLS=OFF -DLLVM_TEMPORARILY_ALLOW_OLD_TOOLCHAIN=OFF -DLLVM_TARGETS_TO_BUILD="X86" -DLLVM_LINK_LLVM_DYLIB=ON -DCOMPILER_RT_INCLUDE_TESTS:BOOL=OFF -DLLVM_ENABLE_ASSERTIONS:BOOL=OFF ..\llvm-12.0.1.src\
# λ cmake --build . --target LLVMSupport LLVMCore LLVMIRReader LLVMVisualizers LLVMMC -j7
# λ C:\Users\notify\Desktop\vcpkg-2021.05.12\vcpkg.exe install gflags:x64-windows glog:x64-windows spdlog:x64-windows

# λ cmake.exe -G "Visual Studio 16 2019" -T ClangCL -DCMAKE_PREFIX_PATH="C:\Users\notify\Desktop\llvm-build" -DCMAKE_TOOLCHAIN_FILE=C:\Users\notify\Desktop\vcpkg-2021.05.12\scripts\buildsystems\vcpkg.cmake Z:\reTR
# λ -DDEBUG_GABLE=ON -DZ3_BUILD_LIBZ3_SHARED=ON -DZ3_USE_LIB_GMP=OFF -DZ3_SINGLE_THREADED=OFF
#  rm -rf CMakeCache.txt CMakeFiles\
# λ cd valgrind-3.17.0 && clang -emit-llvm -I valgrind-3.17.0\VEX -I valgrind-3.17.0\VEX\priv\ -I valgrind-3.17.0\VEX\pub -c ..\support\vexops.c  ..\valgrind-3.17.0\VEX\priv\guest_amd64_helpers.c



# WINDESKTOP






cmake_minimum_required (VERSION 3.8)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

project (VMP
        VERSION 1.5.0
        DESCRIPTION "engine"
        LANGUAGES CXX
        )

		
set(VALGRIND_PROJ_DIR "valgrind-3.17.0")

message(STATUS "CMAKE_TOOLCHAIN_FILE is ${CMAKE_TOOLCHAIN_FILE}")

option(DEBUG_GABLE "print cmake info" OFF)
option(BUILD_VALGRIND "BUILD VALGRIND" OFF)
option(BUILD_TRIGGERBUG "BUILD TRIGGERBUG" OFF)
option(BUILD_CRYPTO_ANALYZER "BUILD CRYPTO_ANALYZER" OFF)
option(BUILD_VEXLLVM "BUILD VEXLLVM" OFF)
option(BUILD_PYTHON_FRONTEND "BUILD PYTHON_BLACKEND" OFF)
option(BUILD_TRTEST "BUILD DEVELOP TEST" ON)
#option(BUILD_CFG "BUILD CFG" OFF)


message(STATUS "TR version ${TriggerBug_VERSION} ")

if ("${PROJECT_SOURCE_DIR}" STREQUAL "${PROJECT_BINARY_DIR}")
  message(FATAL_ERROR "In source builds are not allowed. You should invoke "
          "CMake from a different directory.")
endif()


# -Gr __fastcall
# -Ot 代码速度优先
# -Oi inline内部函数
# -O3 优化速度
# /GS 安全检查
# /MD 多线程DLL库
# /Ob2 内联函数扩展 - 任何适用项 inline
# /Ob2  展开标记为 inline 或 __inline 的函数和编译器选择的任何其他函数（由编译器自行进行展开，通常称作自动内联）
# set(EXTINSN -mmmx -msse -msse2 -msse3 -msse4.1 -msse4.2 -mssse3 -mavx -mavx2)

add_definitions(-D_SILENCE_ALL_CXX17_DEPRECATION_WARNINGS)
add_definitions(-D_ENABLE_EXTENDED_ALIGNED_STORAGE)
IF (WIN32)
	MESSAGE(STATUS "Now is windows")
	SET(CMAKE_C_FLAGS_RELEASE   "${CMAKE_C_FLAGS_RELEASE}   /utf-8 /Ob2 /Gr /Ot /Oi /O3 /GS- ")
	SET(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} /utf-8 /Ob2 /Gr /Ot /Oi /O3 /GS- ")
	add_definitions(/arch:AVX2)
	# add_compile_options(-ftrack-macro-expansion=0 -fno-diagnostics-show-caret)
else()
	SET(CMAKE_C_FLAGS_RELEASE   "${CMAKE_C_FLAGS_RELEASE}   -O3 -openmp -Qopenmp -Wall")
	SET(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3 -openmp -Qopenmp -Wall")
	add_compile_options(-fdeclspec 
					-fms-extensions
					-fms-compatibility-version=19.00
					-fdiagnostics-show-template-tree
					-fimplicit-templates
					)
ENDIF ()
#  -fms-extensions open Microsoft extension (to support explicit constructor calls)
# https://clang.llvm.org/docs/UsersManual.html
add_compile_options(
					# -fdelayed-template-parsing add it after libz3
					-Wno-microsoft-explicit-constructor-call
					-Wno-microsoft-unqualified-friend
					-Wno-ambiguous-member-template
					-Wno-extern-c-compat
					-Wno-microsoft-template
					-Wno-format
					-Wno-switch
					-Wno-unused-variable
					)

add_compile_options(-fdelayed-template-parsing)

set(TR_COMPONENT_CXX_FLAGS "")			
if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Intel"))
	set(SSE_FLAGS "-mfpmath=sse" "-msse" "-msse2")
	set(AVX_FLAGS "-mavx" "-mavx2")
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Intel")
	set(SSE_FLAGS "-mfpmath=sse" "-msse" "-msse2" )
	set(AVX_FLAGS "-mavx" "-mavx2")
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
	set(SSE_FLAGS "/arch:SSE2")
	set(AVX_FLAGS "/arch:AVX2")
else()
	message(FATAL_ERROR "Unknown compiler ${CMAKE_CXX_COMPILER_ID}")
endif()
include(CheckCXXCompilerFlag)
check_cxx_compiler_flag("-msse2" HAS_SSE2)
if (${HAS_SSE2})
	add_definitions(${SSE_FLAGS})
else()
	message(WARNING "your operating system does not support ${SSE_FLAGS} vector extensions")
endif()
check_cxx_compiler_flag("-mavx2" HAS_AVX2)
if (${HAS_AVX2})
	add_definitions(${AVX_FLAGS})
else()
	message(WARNING "your operating system does not support ${AVX_FLAGS} vector extensions")
endif()
unset(SSE_FLAGS)
unset(AVX_FLAGS)



# 加入一个配置头文件，用于处理 CMake 对源码的设置
#configure_file (
#   "${PROJECT_SOURCE_DIR}/config.h.in"
#   "${PROJECT_BINARY_DIR}/config.h"
#   )




include(cmake/tr_add_project.cmake)

#install
set(CMAKE_INSTALL_DIR ${CMAKE_BINARY_DIR})
set(CMAKE_INSTALL_INCLUDEDIR "include")
set(CMAKE_C_COMPILE_OBJECT "")


#lib search path
link_directories(${CMAKE_BINARY_DIR}/lib)

SET(CMAKE_INCLUDE_PATH ${CMAKE_SOURCE_DIR}/include/)

# add include path
TR_add_include(libvalgrind ${VALGRIND_PROJ_DIR}/VEX/ priv/ pub/)




# The package gflags:x64-windows provides CMake targets:
find_package(LLVM CONFIG REQUIRED)

SET(LLVMVISUALIZERS_PATH support/LLVMVisualizers/)
SET(LLVM_ADD_NATIVE_VISUALIZERS_TO_SOLUTION TRUE)
add_subdirectory(${LLVMVISUALIZERS_PATH})

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "Using LLVMVisualizers in: ${LLVMVISUALIZERS_PATH}")


# The package gflags:x64-windows provides CMake targets:
find_package(gflags CONFIG REQUIRED)
# target_link_libraries(main PRIVATE gflags_shared gflags::gflags_shared)

# The package glog:x64-windows provides CMake targets:
find_package(glog CONFIG REQUIRED)
# target_link_libraries(main PRIVATE glog::glog)

# The package spdlog:x64-windows provides CMake targets:
find_package(spdlog CONFIG REQUIRED)
# target_link_libraries(main PRIVATE spdlog::spdlog spdlog::spdlog_header_only)

# The package z3:x64-windows provides CMake targets:
find_package(Z3 CONFIG REQUIRED)
# target_link_libraries(main PRIVATE z3::libz3)



TR_lib_add(threadPool "src/thread_pool" ON)
TR_lib_add(libvalgrind ${VALGRIND_PROJ_DIR}/VEX/ BUILD_VALGRIND)
TR_lib_add(libtriggerBug "src/engine" BUILD_TRIGGERBUG)
TR_lib_add(libcryptoAnalyzer "src/crypto_analyzer" BUILD_CRYPTO_ANALYZER)
TR_lib_add(libvexllvm "src/vexllvm" BUILD_VEXLLVM)

TR_lib_add(TRtest "src/test" BUILD_TRTEST)
#TR_lib_add(libcfg "src/CFG" BUILD_CFG)

IF (${BUILD_PYTHON_FRONTEND})
	find_library(TR_PYTHON3_LIB_PATH python3)
	IF(NOT TR_PYTHON3_LIB_PATH)
		MESSAGE(FATAL_ERROR "TriggerBug: python3.x dir not found")
	ENDIF(NOT TR_PYTHON3_LIB_PATH) 
	MESSAGE(STATUS ${TR_PYTHON3_LIB_PATH} " found")
	TR_lib_add(libpythonfront "src/python" BUILD_PYTHON_FRONTEND)
ENDIF()

