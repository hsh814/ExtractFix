#!/bin/bash
compile_type=$1

subject=nm_new
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/klee
export LLVM_COMPILER=clang
make #-j32 &> /dev/null

# copy target to root dir
cp binutils/${subject} ../

if [ $compile_type == 'to_bc' ];
then
    cd binutils
    extract-bc ${subject}

    cd ../..
    # copy target bc to root dir
    cp klee/tools/${subject}.bc .
fi

cd ..
