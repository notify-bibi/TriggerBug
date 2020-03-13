
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
        find_library(
            ${target_name}
            NAMES ${target_name}
            HINTS ${CMAKE_INSTALL_LIBDIR} ${LIB_PATH}
            )
        IF(NOT ${target_name})
            MESSAGE(STATUS "[--------] TriggerBug::${CMAKE_INSTALL_LIBDIR}/${target_name} not found")
            add_subdirectory(${subdir})
            if (NOT(TARGET ${target_name}))
                message(FATAL_ERROR "Target \"${target_name}\" does not exist")
            endif()
        ELSE()
            MESSAGE(STATUS "[++++++++] TriggerBug::${CMAKE_INSTALL_LIBDIR}/${target_name} found")
        ENDIF()
    ENDIF()
    if (TARGET ${target_name})
        set(DIR_HDRS)
        _TR_find_header_(DIR_HDRS ${subdir} "*.h;*.hpp")
        set_target_properties(${target_name} PROPERTIES PUBLIC_HEADER "${DIR_HDRS}")
        SET_TARGET_PROPERTIES(${target_name} PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${BUILD_RUNTIME_OUTPUT_DIRECTORY})
        
        STRING(REGEX REPLACE ".+/(.+)" "\\1" FILE_DIR ${subdir})
        MESSAGE(STATUS "[........] build ${target_name} PUBLIC_HEADER >> ${CMAKE_INCLUDE_PATH}${FILE_DIR}")
        unset(DIR_HDRS)
        install(TARGETS ${target_name}
           RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
           LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
           ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
           PUBLIC_HEADER DESTINATION ${CMAKE_INCLUDE_PATH}${FILE_DIR}
        )
        unset(FILE_DIR)
    endif() 
endmacro()

function(TR_add_include target_name subdir )
    set(lst ${subdir})
    foreach(arg IN LISTS ARGN)
        list(INSERT lst -1 "${subdir}${arg}")
    endforeach()
    set(INCLUDE_${target_name} ${lst} CACHE STRING INTERNAL)
    message(STATUS INCLUDE_${target_name})
endfunction()



macro(TR_ADD_INCLUDE_DIRECTORIES target_name)
    message(STATUS "    INCLUDE_DIRECTORIES:${target_name}")
    foreach(target ${ARGN})
        foreach(include_path IN LISTS INCLUDE_${target})
            set(var "${CMAKE_SOURCE_DIR}/${include_path}")
            INCLUDE_DIRECTORIES(${var})
            message(STATUS "        add ${include_path}")
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
            message(STATUS "    CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS ON")
            set(CMAKE_ENABLE_EXPORTS ON)
            set(CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS ON)
        ENDIF()
        ADD_LIBRARY(${LIB_TARGET} ${LIB_CONFIGURE_TYPE} ${LIB_SOURCES})
    ENDIF()
    target_compile_options(${LIB_TARGET} PRIVATE -O3 -Ob2 -openmp)
                                              
    message(STATUS "    add files  ${LIB_TARGET} ")
    foreach(cfile ${LIB_SOURCES})
        message(STATUS "        add ${cfile} ")
    endforeach()
    
    INCLUDE_DIRECTORIES(.)
    INCLUDE_DIRECTORIES("${CMAKE_INCLUDE_PATH}")
    INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/src")
    message(STATUS "    INCLUDE_DIRECTORIES:${LIB_TARGET}")
    foreach(dependent_target ${LIB_REQUIRE})
        TARGET_LINK_LIBRARIES(${LIB_TARGET} ${dependent_target})
        foreach(include_path IN LISTS INCLUDE_${dependent_target})
            message(STATUS "        add ${include_path}")
            INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/${include_path}")
        endforeach()
    endforeach()
    foreach(include_path IN LISTS INCLUDE_${LIB_TARGET})
        message(STATUS "        add ${include_path}")
        INCLUDE_DIRECTORIES("${CMAKE_SOURCE_DIR}/${include_path}")
    endforeach()
endmacro()
