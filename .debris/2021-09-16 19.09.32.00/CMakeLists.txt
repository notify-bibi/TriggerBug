project(libvalgrind CXX C)


ADD_DEFINITIONS(-DVGA_x86     )
ADD_DEFINITIONS(-DVGA_amd64   )
ADD_DEFINITIONS(-DVGA_ppc32   )
ADD_DEFINITIONS(-DVGA_ppc64be )
ADD_DEFINITIONS(-DVGA_ppc64le )
#ADD_DEFINITIONS(-DVGA_s390x   )
ADD_DEFINITIONS(-DVGA_arm     )
ADD_DEFINITIONS(-DVGA_arm64   )
ADD_DEFINITIONS(-DVGA_mips32  )
ADD_DEFINITIONS(-DVGA_mips64  )
ADD_DEFINITIONS(-DVGA_nanomips)
ADD_DEFINITIONS(-DVEXMULTIARCH)

TR_add_library(TARGET libvalgrind CONFIGURE_TYPE SHARED SOURCESDIR priv)

# set_target_properties(libvalgrind PROPERTIES PUBLIC_HEADER "some.h;another.h")

target_include_directories(libvalgrind PRIVATE ${CMAKE_CURRENT_LIST_DIR}/priv)
target_include_directories(libvalgrind PUBLIC ${CMAKE_CURRENT_LIST_DIR}/pub)

# install(
#     DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
#     DESTINATION ${CMAKE_INSTALL_PREFIX}
#     FILES_MATCHING 
#     PATTERN "*.h"
#     PATTERN "*.hpp"
#     PATTERN "xxxx" EXCLUDE
# )


message(FATAL_ERROR "gggggggggg ${CMAKE_INSTALL_PREFIX}")
