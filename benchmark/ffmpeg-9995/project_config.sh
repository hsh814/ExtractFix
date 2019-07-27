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
    cflags="$cflags -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-no-replace-globals -mllvm -lowfat-symbolize -lstlimpl"
fi

CC=$compiler
CXX=${CC}++
CFLAGS="$cflags"
CXXFLAGS="$cflags"


FFMPEG_DEPS_PATH=../ffmpeg_deps/libs 

#PKG_CONFIG_PATH="$FFMPEG_DEPS_PATH/lib/pkgconfig" ../configure --target-os=linux --disable-shared --enable-static --disable-ffmpeg --disable-ffplay --disable-ffprobe --disable-ffserver --disable-avdevice --disable-doc --disable-symver --arch=x86_64 --enable-cross-compile --sysroot=$SYSROOT --extra-cflags="$CFLAGS" --extra-ldflags="$LDFLAGS" --cc=${CC} --cxx=${CXX}

PKG_CONFIG_PATH="$FFMPEG_DEPS_PATH/lib/pkgconfig" CFLAGS="-I$FFMPEG_DEPS_PATH/include $CFLAGS" ../configure \
    --cc=$CC --cxx=$CXX --ld="$CXX $CXXFLAGS -std=c++11" \
    --extra-ldflags="-L$FFMPEG_DEPS_PATH/lib" \
    --prefix="$FFMPEG_DEPS_PATH" \
    --pkg-config-flags="--static" \
    --enable-ossfuzz \
    --libfuzzer=$LIB_FUZZING_ENGINE \
    --optflags= \
    --enable-gpl \
    --enable-libass \
    --enable-libfdk-aac \
    --enable-libfreetype \
    --enable-libmp3lame \
    --enable-libopus \
    --enable-libtheora \
    --enable-libvorbis \
    --enable-libvpx \
    --enable-libx264 \
    --enable-libx265 \
    --enable-nonfree \
    --disable-muxers \
    --disable-protocols \
    --disable-devices \
    --disable-shared \
    --enable-cross-compile \
    --arch=x86_64 \
    --target-os=linux

cd ../..


