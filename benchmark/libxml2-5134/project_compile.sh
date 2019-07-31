#!/bin/bash

source=$1
target=$2

current_dir=`pwd`
cd project
KLEE_CFLAGS="-L${current_dir}/project_specific_lib/"
PROJECT_CFLAGS=" -I${current_dir}/project/include -L${current_dir}/project/.lib/ -lz -llzma -lm -ldl"
clang ${source} $PROJECT_CFLAGS $KLEE_CFLAGS -o ${target}
cd ..

