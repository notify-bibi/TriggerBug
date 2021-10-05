# CMakeList.txt: TriggerBug 的 CMake 项目，在此处包括源代码并定义
# 项目特定的逻辑。
#
cmake_minimum_required (VERSION 3.8)
project(QCFGView CXX)

# 将源代码添加到此项目的可执行文件。

set(CMAKE_AUTOMOC ON)
set(CMAKE_INCLUDE_CURRENT_DIR ON)

set(CMAKE_PREFIX_PATH "C:\\Qt\\Qt5.12.1\\5.12.1\\msvc2017_64\\")        # 非常重要！只有路径对了，qt5能找到所有的modules

find_package(Qt5Widgets REQUIRED)
LINK_DIRECTORIES("${PROJECT_SOURCE_DIR}/../../lib")
LINK_DIRECTORIES("C:\\Qt\\Qt5.12.1\\5.12.1\\msvc2017_64\\lib")
INCLUDE_DIRECTORIES("./")


SET(QCFGView_INCLUDE ${PROJECT_SOURCE_DIR}/../../include/)
INCLUDE_DIRECTORIES(${CMAKE_PREFIX_PATH})
INCLUDE_DIRECTORIES(${QCFGView_INCLUDE})
INCLUDE_DIRECTORIES("${QCFGView_INCLUDE}/Valgrind/priv/")
INCLUDE_DIRECTORIES("${QCFGView_INCLUDE}/Valgrind/pub/")
INCLUDE_DIRECTORIES("${QCFGView_INCLUDE}/Z3Header/")



INCLUDE_DIRECTORIES("C:\\Qt\\Qt5.12.1\\5.12.1\\msvc2017_64\\include")
INCLUDE_DIRECTORIES(".\\GeneratedFiles\\Debug")
INCLUDE_DIRECTORIES("C:\\Qt\\Qt5.12.1\\5.12.1\\msvc2017_64\\include\\QtCore")
INCLUDE_DIRECTORIES("C:\\Qt\\Qt5.12.1\\5.12.1\\msvc2017_64\\include\\QtGui")
INCLUDE_DIRECTORIES("C:\\Qt\\Qt5.12.1\\5.12.1\\msvc2017_64\\include\\QtANGLE")
INCLUDE_DIRECTORIES("C:\\Qt\\Qt5.12.1\\5.12.1\\msvc2017_64\\include\\QtWidgets")





add_executable(QCFGView  "main.cpp")

add_library(CFGClass "CFG.cpp" "CFG.h" "QCFGBasictypes.h")
add_library(QCFGGraphicsSceneClass "QCFGGraphicsScene.cpp" "QCFGGraphicsScene.h" "QCFGBasictypes.h")
add_library(QCFGGraphicsTextItem "QCFGGraphicsTextItem.cpp" "QCFGGraphicsTextItem.h" "QCFGBasictypes.h")
add_library(QCFGGraphicsView "QCFGGraphicsView.cpp" "QCFGGraphicsView.h" "QCFGBasictypes.h")
add_library(QCFGPathConnect "QCFGPathConnect.cpp" "QCFGPathConnect.h" "QCFGBasictypes.h")
add_library(QCFGStateView "QCFGStateView.cpp" "QCFGStateView.h" "QCFGBasictypes.h")


find_library(TriggerBug_LIBRARY TriggerBug ${PROJECT_BINARY_DIR}/../src/TriggerBug)
message("cfg: PROJECT_BINARY_DIR : ${PROJECT_BINARY_DIR}")
message("cfg: TriggerBug lib dir: ${TriggerBug_LIBRARY}")
message("cfg: CMAKE_PREFIX_PATH dir: ${CMAKE_PREFIX_PATH}")
LINK_DIRECTORIES(${TriggerBug_LIBRARY})
TARGET_LINK_LIBRARIES(QCFGView CFGClass QCFGGraphicsSceneClass QCFGGraphicsTextItem QCFGGraphicsView QCFGPathConnect QCFGStateView TriggerBug qtmaind Qt5Cored Qt5Guid Qt5Widgetsd)

# TODO: 如有需要，请添加测试并安装目标。
