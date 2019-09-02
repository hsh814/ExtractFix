#!/bin/bash
compile_type=$1
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

subject=stack_overflow
current_dir=`pwd`
cd project

cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -Wno-everything"

if [ $compile_type == 'to_bc' ];
then
    # required by wllvm
    export LLVM_COMPILER=clang
    compiler=wllvm
elif [ $compile_type == 'lowfat' ];
then
    compiler=${LOWFAT_CLANG}
    cflags="$cflags -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-symbolize -lstlimpl"
fi
$compiler ${subject}.c $cflags -o ${subject}

if [ $compile_type == 'to_bc' ];
then
    KLEE_CFLAGS="-lkleeRuntest -lkleeBasic"
    $compiler ${subject}.c $cflags -c -o ${subject}.o
    wllvm -ggdb3 -Wall -W -o ${subject} ${subject}.o ${KLEE_CFLAGS} -Wl,-rpath
    extract-bc -l /usr/local/bin/llvm-link ${subject}
fi

cd ..
