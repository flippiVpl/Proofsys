cmake_minimum_required(VERSION 3.16)
project(Proofsys)

set(CMAKE_CXX_STANDARD 17)
include(ExternalProject)

if(NOT EXISTS "${CMAKE_SOURCE_DIR}/cadical")
    message(FATAL_ERROR "Cadical submodule not found! Run 'git submodule update --init --recursive'.")
endif()

ExternalProject_Add(
    cadical_build
    SOURCE_DIR ${CMAKE_SOURCE_DIR}/cadical
    CONFIGURE_COMMAND ./configure
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    INSTALL_COMMAND ""
    BUILD_BYPRODUCTS ${CMAKE_SOURCE_DIR}/cadical/build/libcadical.a
)

add_executable(proof main.cpp)
target_include_directories(proof PRIVATE ${CMAKE_SOURCE_DIR}/cadical/src)
target_link_libraries(proof ${CMAKE_SOURCE_DIR}/cadical/build/libcadical.a)
add_dependencies(proof cadical_build)