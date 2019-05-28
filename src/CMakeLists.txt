cmake_minimum_required(VERSION 3.4.3)
project (main)
add_executable(main
        main.cpp
        synthesis/Synthesizer.cpp
        fault_localization/FixLocation.cpp
        Global.cpp)
