#!/bin/bash
compile_type=$1

subject=split
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/klee
export LLVM_COMPILER=clang
make -j32 &> /dev/null
make src/${subject} -j32 &> /dev/null

# copy target to root dir
cp src/$subject ../

if [ $compile_type == 'to_bc' ];
then
    cd src
    KLEE_CFLAGS="-lkleeRuntest -lkleeBasic -lhook -L${current_dir}/project_specific_lib/"
    PROJECT_CFALGS="-"
    # wllvm -ggdb3 -Wall -W -o ${subject} ${subject}.o ${PROJECT_CFALGS} ${KLEE_CFLAGS} -Wl,-rpath
    extract-bc -l /usr/local/bin/llvm-link ${subject}

    cd ../..
    # copy target bc to root dir
    cp klee/src/${subject}.bc .
fi

cd ..

