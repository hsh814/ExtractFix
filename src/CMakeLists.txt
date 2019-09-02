cmake_minimum_required(VERSION 3.4.3)
project (main)

# Boost
set(Boost_USE_MULTITHREADED OFF)
FIND_PACKAGE( Boost 1.40 COMPONENTS program_options log REQUIRED )
INCLUDE_DIRECTORIES( ${Boost_INCLUDE_DIR} )
ADD_DEFINITIONS(-DBOOST_LOG_DYN_LINK)

# Jsoncpp
find_package(PkgConfig REQUIRED)
pkg_check_modules(JSONCPP jsoncpp)
link_libraries(${JSONCPP_LIBRARIES})

# Compiler
set(CMAKE_CXX_FLAGS "-lboost_program_options") #added on 29 Sep 2017
set(CMAKE_CXX_STANDARD 11) # C++11...
set(CMAKE_CXX_STANDARD_REQUIRED ON) #...is required...
set(CMAKE_CXX_EXTENSIONS OFF) #...without compiler extensions like gnu++11

if(NOT DEFINED ENV{LLVM_HOME})
    message(FATAL_ERROR "$LLVM_HOME is not defined")
else ()
    set(ENV{LLVM_DIR} $ENV{LLVM_HOME}/lib/cmake/llvm)
endif()

find_package(LLVM REQUIRED CONFIG)
add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_subdirectory(fault_localization)
add_subdirectory(tools)
add_subdirectory(util)
add_subdirectory(sanitizer)
add_subdirectory(instrumentation)

configure_file(ExtractFix.py ExtractFix.py COPYONLY)
configure_file(runtime.py runtime.py COPYONLY)
configure_file(Global.py Global.py COPYONLY)
configure_file(__init__.py __init__.py COPYONLY)
file(COPY synthesis DESTINATION .)
