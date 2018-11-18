cmake_minimum_required(VERSION 3.12)
project(mallocproj_handout C)

set(CMAKE_C_STANDARD 11)

include_directories(.)

add_executable(mallocproj_handout
        config.h
        fsecs.c
        fsecs.h
        mdriver.c
        memlib.c
        memlib.h
        mm.c
        mm.h)
