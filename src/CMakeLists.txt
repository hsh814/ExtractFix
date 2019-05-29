cmake_minimum_required(VERSION 3.4.3)
project (main)

# Boost
set(Boost_USE_MULTITHREADED OFF)
FIND_PACKAGE( Boost 1.40 COMPONENTS program_options log REQUIRED )
INCLUDE_DIRECTORIES( ${Boost_INCLUDE_DIR} )
ADD_DEFINITIONS(-DBOOST_LOG_DYN_LINK)

# Compiler
set(CMAKE_CXX_FLAGS "-lboost_program_options") #added on 29 Sep 2017
set(CMAKE_CXX_STANDARD 11) # C++11...
set(CMAKE_CXX_STANDARD_REQUIRED ON) #...is required...
set(CMAKE_CXX_EXTENSIONS OFF) #...without compiler extensions like gnu++11

add_executable(main
        main.cpp
        synthesis/Synthesizer.cpp
        fault_localization/FixLocation.cpp
        Runtime.cpp
        util/WeakestPrecondition.cpp
        Global.cpp)

target_link_libraries(main
        ${Boost_LIBRARIES})