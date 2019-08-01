#!/bin/bash
compile_type=$1

current_dir=`pwd`


cd project
#git checkout 8d34b45

# TODO: coreutils must run ./bootstrap once after checkout
#./bootstrap

# create build diretory and config
rm -rf klee
mkdir klee
cd klee

cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -I${current_dir}/project_specific_lib/ -lhook -L${current_dir}/project_specific_lib/ -Wno-everything"

if [ $compile_type == 'to_bc' ];
then
    # required by wllvm
    export LLVM_COMPILER=clang
    compiler=wllvm
elif [ $compile_type == 'lowfat' ];
then
    compiler=${LOWFAT_CLANG}
    cflags="$cflags -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-memcpy-overlap -mllvm -lowfat-symbolize -lstlimpl"
fi

CC=$compiler ../configure --disable-nls CFLAGS="$cflags"

cd ../..


