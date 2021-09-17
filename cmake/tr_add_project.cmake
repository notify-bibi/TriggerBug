
include (CMakeParseArguments)

macro(TR_add_subdir target_name subdir need_build)
    CMAKE_PARSE_ARGUMENTS(
        LIB
        ""
        ""
        "PATH"
        ${ARGN}
    )
    message(STATUS "Generating ${target_name}")
    set("DIRECTORY_${target_name}" ${subdir})
    IF(${need_build})
        message(STATUS "add_subdirectory ${subdir}")
        add_subdirectory(${subdir})
        if (NOT(TARGET ${target_name}))
            message(FATAL_ERROR "Target \"${target_name}\" does not exist")
        endif()
    ELSE()
		set(lib_hint ${LIB_PATH} "${CMAKE_SOURCE_DIR}/lib" "${CMAKE_SOURCE_DIR}/bin" "${CMAKE_INSTALL_DIR}/bin/" "${CMAKE_INSTALL_DIR}/lib/")
        message(STATUS "find_library ${target_name}")
        find_library(
                ${target_name}
                NAMES ${target_name}
                PATHS ${lib_hint}
                PATH_SUFFIXES lib
        )
        IF(NOT ${target_name})
			message(STATUS "[+++++] Target \"${target_name}\" does not exist try to make" )
			
			# 不存在就构建
            message(STATUS "add_subdirectory ${subdir}")
			add_subdirectory(${subdir})
            if (NOT(TARGET ${target_name}))
				IF(${DEBUG_GABLE})
					MESSAGE(STATUS "[--------] TriggerBug:: ${target_name} not found \nhints:${lib_hint}")
				ENDIF()
                message(FATAL_ERROR "[--------] Target \"${target_name}\" does not exist " )
            endif()
        ELSE()
			IF(${DEBUG_GABLE}) 
				MESSAGE(STATUS "[++++++++] TriggerBug:: ${target_name} found")
			ENDIF()
		ENDIF()
    ENDIF()
    if (TARGET ${target_name})
        # ---------------------------------------------------------------------------------------
		# Include files
		# ---------------------------------------------------------------------------------------
		install(DIRECTORY include/ DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}" PATTERN "fmt/bundled" EXCLUDE)
		install(
			TARGETS ${target_name}
			EXPORT ${target_name}
			LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
			ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
			RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
		
    endif() 
	
endmacro()



# macro(TR_ADD_INCLUDE_DIRECTORIES target_name)
	# IF(${DEBUG_GABLE}) 
		# message(STATUS "    INCLUDE_DIRECTORIES:${target_name}")
    # ENDIF()
	# foreach(target ${ARGN})
        # foreach(include_path IN LISTS INCLUDE_${target})
            # set(var "${CMAKE_SOURCE_DIR}/${include_path}")
            # INCLUDE_DIRECTORIES(${var})
            # IF(${DEBUG_GABLE}) 
				# message(STATUS "        add ${include_path}")
			# ENDIF()
		# endforeach()
    # endforeach()
# endmacro()

macro(TR_add_library)
    CMAKE_PARSE_ARGUMENTS(
        LIB 
        ""
        "TARGET;CONFIGURE_TYPE;SOURCESDIR"
        "SOURCES"
        ${ARGN}
    )
    
    IF(NOT LIB_SOURCESDIR)
        SET(LIB_SOURCESDIR .)
    ENDIF()
    
    IF(NOT ("${LIB_SOURCES}" MATCHES "c"))
        aux_source_directory(${LIB_SOURCESDIR} LIB_SOURCES)
    ENDIF()
    
    IF((LIB_CONFIGURE_TYPE EQUAL False) OR (NOT LIB_CONFIGURE_TYPE))
        message(STATUS "add_executable  ${LIB_TARGET}")
        ADD_EXECUTABLE(${LIB_TARGET} ${LIB_SOURCES})   
    ELSE()
        message(STATUS "add_library  ${LIB_TARGET} ${LIB_CONFIGURE_TYPE}")
        IF(LIB_CONFIGURE_TYPE MATCHES "SHARED")
			set(CMAKE_ENABLE_EXPORTS ON)
			IF (WIN32)
				IF(${DEBUG_GABLE}) 
					message(STATUS "    CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS ON")
				ENDIF()
				set(CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS ON)
			ENDIF()
        ENDIF()
        add_library(${LIB_TARGET} ${LIB_CONFIGURE_TYPE} ${LIB_SOURCES})
    ENDIF()

	IF(${DEBUG_GABLE}) 
		message(STATUS "    add files  ${LIB_TARGET} ")
	ENDIF()
    foreach(cfile ${LIB_SOURCES})
        IF(${DEBUG_GABLE}) 
			message(STATUS "        + ${cfile} ")
		ENDIF()
	endforeach()
    
    # INCLUDE_DIRECTORIES(.)
    target_include_directories(${LIB_TARGET} PUBLIC  "$<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/include>" "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>")
    # target_include_directories(${LIB_TARGET} PRIVATE "$<BUILD_INTERFACE:${CMAKE_SOURCE_DIR}/src;${CMAKE_CURRENT_LIST_DIR}>" "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>")
	
endmacro()
