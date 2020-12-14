
include (CMakeParseArguments)

macro(_TR_find_header_ HDRS root_dir suffixlst)
    foreach(suffix  ${suffixlst})
        file(GLOB_RECURSE DIRS ${root_dir}/${suffix})
        list(APPEND ${HDRS} ${DIRS})
        unset(DIRS)
    endforeach()
endmacro()

macro(TR_lib_add target_name subdir need_build)
    CMAKE_PARSE_ARGUMENTS(
        LIB
        ""
        ""
        "PATH"
        ${ARGN}
    )
    set("DIRECTORY_${target_name}" ${subdir})
    IF(${need_build})
        add_subdirectory(${subdir})
        if (NOT(TARGET ${target_name}))
            message(FATAL_ERROR "Target \"${target_name}\" does not exist")
        endif()
    ELSE()
		set(lib_hint ${LIB_PATH} "${CMAKE_SOURCE_DIR}/lib" "${CMAKE_SOURCE_DIR}/bin" "${CMAKE_INSTALL_DIR}/bin/" "${CMAKE_INSTALL_DIR}/lib/")
        find_library(
                ${target_name}
                NAMES ${target_name}
                PATHS ${lib_hint}
                PATH_SUFFIXES lib
        )
        IF(NOT ${target_name})
			message(STATUS "[+++++] Target \"${target_name}\" does not exist try to make" )
			
			# 不存在就构建
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

        set(DIR_HDRS)
        _TR_find_header_(DIR_HDRS ${subdir} "*.h;*.hpp")
		
        STRING(REGEX REPLACE ".+/(.+)" "\\1" FILE_DIR ${subdir})
        IF(${DEBUG_GABLE}) 
			MESSAGE(STATUS "[........] build ${target_name} PUBLIC_HEADER >> ${CMAKE_INSTALL_INCLUDEDIR}/${FILE_DIR}")
        ENDIF()
		
		#生成路径
        set_target_properties(${target_name}
		  PROPERTIES
		  ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_INSTALL_DIR}/lib"
		  LIBRARY_OUTPUT_DIRECTORY "${CMAKE_INSTALL_DIR}/lib"
		  RUNTIME_OUTPUT_DIRECTORY "${CMAKE_INSTALL_DIR}/bin"
		)
		
		#target_include_directories(${target_name} PUBLIC ${DIR_HDRS})
		#target_include_directories(${target_name} PRIVATE "src/")
		#target_include_directories(${target_name} PUBLIC $<BUILD_INTERFACE:${CMAKE_INCLUDE_PATH}>)

        install(TARGETS ${target_name}
           # RUNTIME DESTINATION ${CMAKE_INSTALL_DIR}/lib
           # LIBRARY DESTINATION ${CMAKE_INSTALL_DIR}/lib
           # ARCHIVE DESTINATION ${CMAKE_INSTALL_DIR}/bin
		   # PRIVATE_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/${FILE_DIR}
           PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/${FILE_DIR}
        )
		unset(DIR_HDRS)
        unset(FILE_DIR)
    endif() 
	
endmacro()

function(TR_add_include target_name subdir )
    set(lst ${subdir})
    foreach(arg IN LISTS ARGN)
        list(INSERT lst -1 "${subdir}${arg}")
    endforeach()
    set(INCLUDE_${target_name} ${lst} CACHE STRING INTERNAL)
	IF(${DEBUG_GABLE})
		message(STATUS INCLUDE_${target_name})
	ENDIF()
endfunction()



macro(TR_ADD_INCLUDE_DIRECTORIES target_name)
	IF(${DEBUG_GABLE}) 
		message(STATUS "    INCLUDE_DIRECTORIES:${target_name}")
    ENDIF()
	foreach(target ${ARGN})
        foreach(include_path IN LISTS INCLUDE_${target})
            set(var "${CMAKE_SOURCE_DIR}/${include_path}")
            INCLUDE_DIRECTORIES(${var})
            IF(${DEBUG_GABLE}) 
				message(STATUS "        add ${include_path}")
			ENDIF()
		endforeach()
    endforeach()
endmacro()

macro(TR_add_library)
    CMAKE_PARSE_ARGUMENTS(
        LIB 
        ""
        "TARGET;CONFIGURE_TYPE;SOURCESDIR"
        "SOURCES;REQUIRE"
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
    # target_compile_options(${LIB_TARGET} PRIVATE -O3 -openmp)
    # IF (WIN32)
        # target_compile_options(${LIB_TARGET} PRIVATE -Ob2)
    # ENDIF ()
	IF(${DEBUG_GABLE}) 
		message(STATUS "    add files  ${LIB_TARGET} ")
	ENDIF()
    foreach(cfile ${LIB_SOURCES})
        IF(${DEBUG_GABLE}) 
			message(STATUS "        + ${cfile} ")
		ENDIF()
	endforeach()
    
    INCLUDE_DIRECTORIES(.)
    INCLUDE_DIRECTORIES("${CMAKE_INCLUDE_PATH}")
    INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src")
	IF(${DEBUG_GABLE}) 
		message(STATUS "    INCLUDE_DIRECTORIES:${LIB_TARGET}")
	ENDIF()
    foreach(dependent_target ${LIB_REQUIRE})
        TARGET_LINK_LIBRARIES(${LIB_TARGET} ${dependent_target})
        foreach(include_path IN LISTS INCLUDE_${dependent_target})
            IF(${DEBUG_GABLE}) 
				message(STATUS "        add ${include_path}")
			ENDIF()
            INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/${include_path}")
        endforeach()
    endforeach()
    foreach(include_path IN LISTS INCLUDE_${LIB_TARGET})
        IF(${DEBUG_GABLE}) 
			message(STATUS "        add ${include_path}")
        ENDIF()
		INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/${include_path}")
    endforeach()
endmacro()
