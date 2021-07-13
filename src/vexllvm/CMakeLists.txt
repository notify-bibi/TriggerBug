if(0)
	find_package(LLVM REQUIRED CONFIG)

	message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
	message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

	# Set your project compile flags.
	# E.g. if using the C++ header files
	# you will need to enable C++11 support
	# for your compiler.

	include_directories(${LLVM_INCLUDE_DIRS})
	add_definitions(${LLVM_DEFINITIONS})
endif()

TR_add_library( TARGET libvexllvm 
                CONFIGURE_TYPE SHARED
				REQUIRE libvalgrind
              )