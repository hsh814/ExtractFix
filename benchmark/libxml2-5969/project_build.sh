#!/bin/bash
compile_type=$1

subject=xmllint
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/
export LLVM_COMPILER=clang
make -j32 &> /dev/null


cd ..
