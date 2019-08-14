#!/bin/bash
compile_type=$1

subject=djpeg
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/klee
export LLVM_COMPILER=clang
make -j32 &> /dev/null

# copy target to root dir
cp ./${subject} ../

cd ..
