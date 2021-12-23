@echo off
:: Installs build 
:: λ C:\Users\notify\Desktop\vcpkg-2021.05.12\vcpkg.exe install gflags:x64-windows glog:x64-windows spdlog:x64-windows
:: 
:: λ cmake.exe -G "Visual Studio 16 2019" -T ClangCL -DCMAKE_PREFIX_PATH=C:\Users\24964\Desktop\build-llvm -DCMAKE_TOOLCHAIN_FILE=C:\vcpkg\scripts\buildsystems\vcpkg.cmake Y:\TriggerBug
:: λ -DDEBUG_GABLE=ON -DZ3_BUILD_LIBZ3_SHARED=ON -DZ3_USE_LIB_GMP=OFF -DZ3_SINGLE_THREADED=OFF
::  rm -rf CMakeCache.txt CMakeFiles\
:: λ cd valgrind-3.17.0 && clang -emit-llvm -I valgrind-3.17.0\VEX -I valgrind-3.17.0\VEX\priv\ -I valgrind-3.17.0\VEX\pub -c ..\support\vexops.c  ..\valgrind-3.17.0\VEX\priv\guest_amd64_helpers.c


@echo on

set BUILD64=0A_BUILD64
set GITVCPKG=C:\vcpkg
set PREFIX_PATH=%BUILD64%\_install
set LLVMSRC=Y:\llvm-13.0.1rc1.src
set BUILDLLVM=%cd%\llvm13debug


mkdir %BUILD64%
mkdir %PREFIX_PATH%



git clone https://github.com/microsoft/vcpkg.git %GITVCPKG%
cmake -DCMAKE_BUILD_TYPE=DEBUG -G "Visual Studio 16 2019" -A x64 -T ClangCL -DLLVM_BUILD_TOOLS=ON -DLLVM_TEMPORARILY_ALLOW_OLD_TOOLCHAIN=OFF -DLLVM_TARGETS_TO_BUILD="X86" -DLLVM_LINK_LLVM_DYLIB=ON -DCOMPILER_RT_INCLUDE_TESTS:BOOL=OFF -DLLVM_ENABLE_ASSERTIONS:BOOL=ON -B %BUILDLLVM% %LLVMSRC%
cmake --build %BUILDLLVM% --target LLVMSupport LLVMCore LLVMIRReader LLVMVisualizers LLVMMC llvm-link -j7
cmake -DCMAKE_BUILD_TYPE=DEBUG -G "Visual Studio 16 2019" -A x64 -T ClangCL  -DCMAKE_INSTALL_PREFIX=%PREFIX_PATH% -DVCPKG_TARGET_TRIPLET=x64-windows -DCMAKE_TOOLCHAIN_FILE=%GITVCPKG%\scripts\buildsystems\vcpkg.cmake -DCMAKE_PREFIX_PATH=%BUILDLLVM% -B %BUILD64% %~dp0

call %~dp0\build_install.bat
