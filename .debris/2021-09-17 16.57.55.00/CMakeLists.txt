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



set_property(GLOBAL PROPERTY USE_FOLDERS ON)
set_property(GLOBAL PROPERTY PREDEFINED_TARGETS_FOLDER "CMakePredefinedTargets")


cmake_minimum_required (VERSION 3.8)
project(InstOpt
        VERSION 1.5.0
        DESCRIPTION "engine"
        LANGUAGES CXX
        )

include(CheckCXXCompilerFlag)
include(GNUInstallDirs)
include(cmake/tr_add_project.cmake)

INCLUDE_DIRECTORIES(.)

message(STATUS "CMAKE_TOOLCHAIN_FILE is ${CMAKE_TOOLCHAIN_FILE}")
message(STATUS "CMAKE_INSTALL_INCLUDEDIR is ${CMAKE_INSTALL_INCLUDEDIR}")
message(STATUS "CMAKE_CURRENT_LIST_DIR is ${CMAKE_CURRENT_LIST_DIR}")

# ---------------------------------------------------------------------------------------
# Compiler config
# ---------------------------------------------------------------------------------------
if(NOT CMAKE_CXX_STANDARD)
    set(CMAKE_CXX_STANDARD 17)
    set(CMAKE_CXX_STANDARD_REQUIRED ON)
endif()

set(VALGRIND_PROJ_DIR "src/valgrind-3.17.0")


option(INSTOPT_BUILD_ALL "Build all artifacts" OFF)

# build shared option
option(INSTOPT_BUILD_SHARED "Build shared library" OFF)

# precompiled headers option
option(INSTOPT_ENABLE_PCH "Build static or shared library using precompiled header to speed up compilation time" OFF)

# example options
option(INSTOPT_BUILD_EXAMPLE "Build example" ${INSTOPT_MASTER_PROJECT})
option(INSTOPT_BUILD_EXAMPLE_HO "Build header only example" OFF)

# testing options
option(INSTOPT_BUILD_TESTS "Build tests" OFF)
option(INSTOPT_BUILD_TESTS_HO "Build tests using the header only version" OFF)

# bench options
option(INSTOPT_BUILD_BENCH "Build benchmarks (Requires https://github.com/google/benchmark.git to be installed)" OFF)

# sanitizer options
option(INSTOPT_SANITIZE_ADDRESS "Enable address sanitizer in tests" OFF)

# warning options
option(INSTOPT_BUILD_WARNINGS "Enable compiler warnings" OFF)

# install options
option(INSTOPT_INSTALL "Generate the install target" ${INSTOPT_MASTER_PROJECT})
option(INSTOPT_FMT_EXTERNAL "Use external fmt library instead of bundled" OFF)
option(INSTOPT_FMT_EXTERNAL_HO "Use external fmt header-only library instead of bundled" OFF)
option(INSTOPT_NO_EXCEPTIONS "Compile with -fno-exceptions. Call abort() on any spdlog exceptions" OFF)

if(INSTOPT_FMT_EXTERNAL AND INSTOPT_FMT_EXTERNAL_HO)
    message(FATAL_ERROR "INSTOPT_FMT_EXTERNAL and INSTOPT_FMT_EXTERNAL_HO are mutually exclusive")
endif()




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
	set(SSE_FLAGS "-msse" "-msse2")
	set(AVX_FLAGS "-mavx" "-mavx2")
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Intel")
	set(SSE_FLAGS "-msse" "-msse2" )
	set(AVX_FLAGS "-mavx" "-mavx2")
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
	set(SSE_FLAGS "/arch:SSE2")
	set(AVX_FLAGS "/arch:AVX2")
else()
	message(FATAL_ERROR "Unknown compiler ${CMAKE_CXX_COMPILER_ID}")
endif()
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








# The package gflags:x64-windows provides CMake targets:
find_package(LLVM CONFIG REQUIRED)

SET(LLVMVISUALIZERS_PATH support/LLVMVisualizers/)
SET(LLVM_ADD_NATIVE_VISUALIZERS_TO_SOLUTION TRUE)
add_subdirectory(${LLVMVISUALIZERS_PATH})

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
message(STATUS "Using LLVMVisualizers in: ${LLVMVISUALIZERS_PATH}")


# The package gflags:x64-windows provides CMake targets:
find_package(gflags REQUIRED)
# target_link_libraries(main PRIVATE gflags_shared gflags::gflags_shared)

# The package glog:x64-windows provides CMake targets:
find_package(glog REQUIRED)
# target_link_libraries(main PRIVATE glog::glog)

# The package spdlog:x64-windows provides CMake targets:
find_package(spdlog REQUIRED)
# target_link_libraries(main PRIVATE spdlog::spdlog spdlog::INSTOPT_header_only)

# The package z3:x64-windows provides CMake targets:
find_package(Z3 REQUIRED)
# target_link_libraries(main PRIVATE z3::libz3)
message(STATUS "Z3_FOUND: ${Z3_FOUND}")
message(STATUS "Found Z3 ${Z3_VERSION_STRING}")
message(STATUS "Z3_DIR: ${Z3_DIR}")


target_include_directories(z3::libz3 INTERFACE ${Z3_CXX_INCLUDE_DIRS})
target_include_directories(LLVMCore INTERFACE ${LLVM_INCLUDE_DIRS})
target_compile_definitions(LLVMCore INTERFACE ${LLVM_DEFINITIONS})



TR_add_subdir(threadPool "src/thread_pool" ON)
TR_add_subdir(helper "src/helper" ON)
TR_add_subdir(libvalgrind ${VALGRIND_PROJ_DIR}/VEX/ BUILD_VALGRIND)
TR_add_subdir(libtriggerBug "src/engine" BUILD_TRIGGERBUG)
TR_add_subdir(libcryptoAnalyzer "src/crypto_analyzer" BUILD_CRYPTO_ANALYZER)
TR_add_subdir(libvexllvm "src/vexllvm" BUILD_VEXLLVM)
TR_add_subdir(TRtest "tests" BUILD_TRTEST)
#TR_add_subdir(libcfg "src/CFG" BUILD_CFG)

IF (${BUILD_PYTHON_FRONTEND})
	find_library(TR_PYTHON3_LIB_PATH python3)
	IF(NOT TR_PYTHON3_LIB_PATH)
		MESSAGE(FATAL_ERROR "TriggerBug: python3.x dir not found")
	ENDIF(NOT TR_PYTHON3_LIB_PATH) 
	MESSAGE(STATUS ${TR_PYTHON3_LIB_PATH} " found")
	TR_add_subdir(libpythonfront "src/python" BUILD_PYTHON_FRONTEND)
ENDIF()

# ---------------------------------------------------------------------------------------
# Build binaries
# ---------------------------------------------------------------------------------------
if(INSTOPT_BUILD_EXAMPLE OR INSTOPT_BUILD_EXAMPLE_HO OR INSTOPT_BUILD_ALL)
    message(STATUS "Generating example(s)")
    add_subdirectory(example)
    INSTOPT_enable_warnings(example)
    if(INSTOPT_BUILD_EXAMPLE_HO)
        INSTOPT_enable_warnings(example_header_only)
    endif()
endif()

if(INSTOPT_BUILD_TESTS OR INSTOPT_BUILD_TESTS_HO OR INSTOPT_BUILD_ALL)
    message(STATUS "Generating tests")
    enable_testing()
    add_subdirectory(tests)
endif()

if(INSTOPT_BUILD_BENCH OR INSTOPT_BUILD_ALL)
    message(STATUS "Generating benchmarks")
    add_subdirectory(bench)
endif()


# ---------------------------------------------------------------------------------------
# Install
# ---------------------------------------------------------------------------------------
if(INSTOPT_INSTALL)
    message(STATUS "Generating install")
    set(project_config_in "${CMAKE_CURRENT_LIST_DIR}/cmake/spdlogConfig.cmake.in")
    set(project_config_out "${CMAKE_CURRENT_BINARY_DIR}/spdlogConfig.cmake")
    set(config_targets_file "spdlogConfigTargets.cmake")
    set(version_config_file "${CMAKE_CURRENT_BINARY_DIR}/spdlogConfigVersion.cmake")
    set(export_dest_dir "${CMAKE_INSTALL_LIBDIR}/cmake/spdlog")
    set(pkgconfig_install_dir "${CMAKE_INSTALL_LIBDIR}/pkgconfig")
    set(pkg_config "${CMAKE_BINARY_DIR}/${PROJECT_NAME}.pc")

    # ---------------------------------------------------------------------------------------
    # Include files
    # ---------------------------------------------------------------------------------------
    install(DIRECTORY include/ DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}" PATTERN "fmt/bundled" EXCLUDE)
    install(
        TARGETS spdlog INSTOPT_header_only
        EXPORT spdlog
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})

    if(NOT INSTOPT_FMT_EXTERNAL AND NOT INSTOPT_FMT_EXTERNAL_HO)
        install(DIRECTORY include/${PROJECT_NAME}/fmt/bundled/
                DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}/${PROJECT_NAME}/fmt/bundled/")
    endif()

    # ---------------------------------------------------------------------------------------
    # Install pkg-config file
    # ---------------------------------------------------------------------------------------
    get_target_property(PKG_CONFIG_DEFINES spdlog INTERFACE_COMPILE_DEFINITIONS)
    string(REPLACE ";" " -D" PKG_CONFIG_DEFINES "${PKG_CONFIG_DEFINES}")
    string(CONCAT PKG_CONFIG_DEFINES "-D" "${PKG_CONFIG_DEFINES}")
    configure_file("cmake/${PROJECT_NAME}.pc.in" "${pkg_config}" @ONLY)
    install(FILES "${pkg_config}" DESTINATION "${pkgconfig_install_dir}")

    # ---------------------------------------------------------------------------------------
    # Install CMake config files
    # ---------------------------------------------------------------------------------------
    install(EXPORT spdlog DESTINATION ${export_dest_dir} NAMESPACE spdlog:: FILE ${config_targets_file})

    include(CMakePackageConfigHelpers)
    configure_file("${project_config_in}" "${project_config_out}" @ONLY)

    write_basic_package_version_file("${version_config_file}" COMPATIBILITY SameMajorVersion)
    install(FILES "${project_config_out}" "${version_config_file}" DESTINATION "${export_dest_dir}")

    # ---------------------------------------------------------------------------------------
    # Support creation of installable packages
    # ---------------------------------------------------------------------------------------
    include(cmake/spdlogCPack.cmake)
endif()


set_target_properties(acc_gen PROPERTIES FOLDER "Utils")
set_target_properties(intrinsics_gen PROPERTIES FOLDER "Utils")
set_target_properties(omp_gen PROPERTIES FOLDER "Utils")