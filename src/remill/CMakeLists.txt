# add everything as public.
set(REMILL_INCLUDE_DIR "${CMAKE_SOURCE_DIR}/include")
set(REMILL_SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}")
set(REMILL_LIB_DIR "${CMAKE_CURRENT_SOURCE_DIR}/lib")





set(REMILL_BUILD_SEMANTICS_DIR_X86 "${CMAKE_CURRENT_BINARY_DIR}/lib/Arch/X86/Runtime")
set(REMILL_BUILD_SEMANTICS_DIR_AARCH32 "${CMAKE_CURRENT_BINARY_DIR}/lib/Arch/AArch32/Runtime")
set(REMILL_BUILD_SEMANTICS_DIR_AARCH64 "${CMAKE_CURRENT_BINARY_DIR}/lib/Arch/AArch64/Runtime")
set(REMILL_BUILD_SEMANTICS_DIR_SPARC32 "${CMAKE_CURRENT_BINARY_DIR}/lib/Arch/SPARC32/Runtime")
set(REMILL_BUILD_SEMANTICS_DIR_SPARC64 "${CMAKE_CURRENT_BINARY_DIR}/lib/Arch/SPARC64/Runtime")


add_library(remill_settings INTERFACE)

target_compile_definitions(remill_settings INTERFACE
  "REMILL_INSTALL_SEMANTICS_DIR=\"${REMILL_INSTALL_SEMANTICS_DIR}\""
  "REMILL_BUILD_SEMANTICS_DIR_X86=\"${REMILL_BUILD_SEMANTICS_DIR_X86}\""
  "REMILL_BUILD_SEMANTICS_DIR_AARCH32=\"${REMILL_BUILD_SEMANTICS_DIR_AARCH32}\""
  "REMILL_BUILD_SEMANTICS_DIR_AARCH64=\"${REMILL_BUILD_SEMANTICS_DIR_AARCH64}\""
  "REMILL_BUILD_SEMANTICS_DIR_SPARC32=\"${REMILL_BUILD_SEMANTICS_DIR_SPARC32}\""
  "REMILL_BUILD_SEMANTICS_DIR_SPARC64=\"${REMILL_BUILD_SEMANTICS_DIR_SPARC64}\""
)

# Intel XED
find_package(XED CONFIG REQUIRED)
add_library(thirdparty_xed INTERFACE)
target_link_libraries(thirdparty_xed INTERFACE
  XED::XED
)

# Google glog module
find_package(glog CONFIG REQUIRED)
add_library(thirdparty_glog INTERFACE)
target_link_libraries(thirdparty_glog INTERFACE
  glog::glog
)

# Google gflags
find_package(gflags CONFIG REQUIRED)
add_library(thirdparty_gflags INTERFACE)
target_link_libraries(thirdparty_gflags INTERFACE
  gflags
)


# LLVM
add_library(thirdparty_llvm INTERFACE)
target_include_directories(thirdparty_llvm SYSTEM INTERFACE
  $<BUILD_INTERFACE:${LLVM_INCLUDE_DIRS}>
)
target_compile_definitions(thirdparty_llvm INTERFACE
  ${LLVM_DEFINITIONS}
)

# Go find only the static libraries of LLVM, and link against those.
# foreach(LLVM_LIB IN LISTS LLVM_AVAILABLE_LIBS)
  # get_target_property(LLVM_LIB_TYPE ${LLVM_LIB} TYPE)
  # if(LLVM_LIB_TYPE STREQUAL "STATIC_LIBRARY")
    # list(APPEND LLVM_LIBRARIES "${LLVM_LIB}")
  # endif()
# endforeach()

# These are out-of-order in `LLVM_AVAILABLE_LIBS` and should always be last.
list(REMOVE_ITEM LLVM_LIBRARIES LLVMMC LLVMCore LLVMSupport)
list(APPEND LLVM_LIBRARIES LLVMMC LLVMCore LLVMSupport LLVMipo)
target_link_libraries(thirdparty_llvm INTERFACE
  ${LLVM_LIBRARIES}
)



# remill_settings
set(THIRDPARTY_LIBRARY_LIST thirdparty_llvm thirdparty_xed thirdparty_glog thirdparty_gflags)
target_link_libraries(remill_settings INTERFACE
  ${THIRDPARTY_LIBRARY_LIST}
)
install(TARGETS remill_settings ${THIRDPARTY_LIBRARY_LIST}
  EXPORT remillTargets)
  
  
  
# INCLUDE_DIRECTORIES(${REMILL_INCLUDE_DIR})
include_directories(remill_os PUBLIC  "$<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/include>" "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>")




add_subdirectory(lib/Arch)
add_subdirectory(lib/BC)
add_subdirectory(lib/OS)
#add_subdirectory(Version)
#set_target_properties(remill_os PROPERTIES FOLDER "Utils")
