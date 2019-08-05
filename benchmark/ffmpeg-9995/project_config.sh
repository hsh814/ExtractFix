#!/bin/bash
compile_type=$1

current_dir="$( cd "$(dirname "$0")" ; pwd -P )"
# get project and set to corresponding version
#git clone https://github.com/vadz/libtiff.git project

cp Makefile project/
cp configure project/
cp /home/nightwish/workspace/bug_repair/crash-free-fix/benchmark/ffmpeg_deps/afl_driver.cpp project/

cd project
#git checkout d9783e4

sed -i 's/av_mallocz(avctx->width \* avctx->height)/malloc(avctx->width * avctx->height)/' libavcodec/dfa.c
sed -i 's/av_cold //' libavcodec/dfa.c
sed -i 's/NULL_IF_CONFIG_SMALL("Chronomaster DFA")/"Chronomaster DFA"/' libavcodec/dfa.c

# create build diretory and config

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


FFMPEG_DEPS_PATH=/home/nightwish/workspace/bug_repair/crash-free-fix/benchmark/ffmpeg_deps/libs

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
    --enable-nonfree \
    --disable-muxers \
    --disable-protocols \
    --disable-devices \
    --disable-shared \
    --enable-cross-compile \
    --arch=x86_64 \
    --target-os=linux

cd ..
