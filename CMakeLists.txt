cmake_minimum_required(VERSION 3.16)

project(MyCadicalProject)

set(CMAKE_CXX_STANDARD 17)

add_subdirectory(cadical)

add_executable(main main.cpp)

target_link_libraries(main cadical)