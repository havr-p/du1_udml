cmake_minimum_required(VERSION 3.24)
project(du1_udml)

set(CMAKE_CXX_STANDARD 17)

add_executable(du1_udml decompose_relation.h decompose_relation.cpp decompose_relation.h)
