#!/bin/bash

source=$1
target=$2

current_dir=`pwd`
cd project
KLEE_CFLAGS="-L${current_dir}/project_specific_lib/"
PROJECT_CFLAGS="${current_dir}/project/.libs/libxml2.a -I${current_dir}/project/include -L${current_dir}/project/.lib/ -lxml2 -lz -llzma -lm -ldl"
clang ${source} $PROJECT_CFLAGS $KLEE_CFLAGS -o ${target}
cd ..
