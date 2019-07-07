#!/bin/bash
set -x
compile_type=$1

current_dir=`pwd`
# get project and set to corresponding version
#git clone https://github.com/vadz/libtiff.git project
cd project
#git checkout d9783e4

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
    cflags="$cflags -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-symbolize -lstlimpl"
fi

CC=$compiler
CXX=${CC}++
CFLAGS="$cflags"
CXXFLAGS="$cflags"

# FFMPEG_DEPS_PATH=../ffmpeg_deps/libs 

PKG_CONFIG_PATH="$FFMPEG_DEPS_PATH/lib/pkgconfig" ../configure --cc="$CC -std=c11 -fPIC" --cxx="$CXX -std=c++11 -fPIC" --ld="$CXX -std=c++11"     --extra-cflags="-I$FFMPEG_DEPS_PATH/include"     --extra-ldflags="-L$FFMPEG_DEPS_PATH/lib"     --prefix="$FFMPEG_DEPS_PATH"     --pkg-config-flags="--static"     --enable-ossfuzz     --libfuzzer=$LIB_FUZZING_ENGINE     --optflags=-O1     --enable-gpl     --enable-libass     --enable-libfreetype       --enable-libopus     --enable-libtheora     --enable-libvorbis     --enable-libvpx     --enable-libx264     --enable-nonfree     --disable-shared --enable-cross-compile

cd ../..


