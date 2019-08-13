#!/bin/bash
compile_type=$1

subject=xmllint
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/
export LLVM_COMPILER=clang
make clean
make -j32 &> /dev/null

# copy target to root dir
#cp ${subject} ../

if [ $compile_type == 'to_bc' ];
then
    KLEE_CFLAGS="-lkleeRuntest -lkleeBasic -lhook -L${current_dir}/project_specific_lib/"
    PROJECT_CFALGS="./.libs/libxml2.a -I./include -L./.libs/ -lxml2 -lz -llzma -lm -ldl"
    wllvm -ggdb3 -Wall -W -o ${subject} ${subject}.o ${PROJECT_CFALGS} ${KLEE_CFLAGS} -Wl,-rpath
    extract-bc -l /usr/local/bin/llvm-link ${subject}

    #cd ..
    # copy target bc to root dir
    #cp klee/${subject}.bc .
fi

cd ..
