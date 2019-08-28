#!/bin/bash
compile_type=$1

current_dir=`pwd`

# get project and set to corresponding version
# git clone https://gitlab.gnome.org/GNOME/libxml2/ project
cd project
#git checkout d9783e4


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
fi

CC=$compiler CFLAGS="$cflags" ./autogen.sh --enable-static # &> /dev/null

cd ..

