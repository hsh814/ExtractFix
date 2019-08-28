#!/bin/bash
compile_type=$1

current_dir=`pwd`


cd project

#TODO: IMPORTANT FOR GETTING configure
#autoreconf -fiv

rm -rf klee
mkdir klee
cd klee

cflags="-g -lkleeRuntest -lkleeBasic -Wno-everything"

if [ $compile_type == 'to_bc' ];
then
    # required by wllvm
    export LLVM_COMPILER=clang
    compiler=wllvm
elif [ $compile_type == 'lowfat' ];
then
    compiler=${LOWFAT_CLANG}
    cflags="$cflags -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-null-deref -mllvm -lowfat-no-check-reads -mllvm -lowfat-no-check-writes -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-check-whole-access -mllvm -lowfat-no-replace-globals -mllvm -lowfat-no-replace-alloca -mllvm -lowfat-no-replace-malloc -mllvm -lowfat-symbolize -lstlimpl"
    #cflags="$cflags -fsanitize=address"
fi

#CC=$compiler cmake -DCMAKE_VERBOSE_MAKEFILE:BOOL=ON -DCMAKE_C_FLAGS_RELEASE="$cflags" ..

CC=$compiler ../configure CFLAGS="$cflags"

cd ../..


