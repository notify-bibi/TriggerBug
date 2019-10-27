cmake_minimum_required (VERSION 3.9)
aux_source_directory(. DIR_tinyxml2_SRCS)
project(tinyxml2 CXX)
add_library(tinyxml2 "tinyxml2.cpp" "tinyxml2.cpp")
