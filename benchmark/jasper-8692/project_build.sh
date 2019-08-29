#!/bin/bash
compile_type=$1

subject=imginfo
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/klee
export LLVM_COMPILER=clang
make -j32 &> /dev/null

# copy target to root dir
cp ./src/appl/${subject} ../

if [ $compile_type == 'to_bc' ];
then
    cd src/appl
    extract-bc -l /usr/local/bin/llvm-link ${subject}

    cd ../../..
    # copy target bc to root dir
    cp klee/src/appl/${subject}.bc .
fi


cd ..
