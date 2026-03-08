cmake_minimum_required(VERSION 3.16)

project(Proofsys)

set(CMAKE_CXX_STANDARD 17)

target_include_directories(main PRIVATE cadical/src)

target_link_libraries(main ${CMAKE_SOURCE_DIR}/cadical/build/libcadical.a)
