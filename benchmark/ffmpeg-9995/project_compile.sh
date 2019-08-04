#!/bin/bash

source=$1
target=$2

current_dir=`pwd`
cd project
KLEE_CFLAGS="-L${current_dir}/project_specific_lib/"
PROJECT_CFLAGS="-lstlimpl -std=c++11 -Llibavcodec -Llibavdevice -Llibavfilter -Llibavformat -Llibavresample -Llibavutil -Llibpostproc -Llibswscale -Llibswresample -L/home/gaoxiang/project/crash-free-fix/benchmark/ffmpeg-9995/../ffmpeg_deps/libs/lib  -Wl,--as-needed -Wl,-z,noexecstack -Wl,--warn-common -Wl,-rpath-link=libpostproc:libswresample:libswscale:libavfilter:libavdevice:libavformat:libavcodec:libavutil:libavresample -Qunused-arguments   libavdevice/libavdevice.a libavfilter/libavfilter.a libavformat/libavformat.a libavcodec/libavcodec.a libpostproc/libpostproc.a libswresample/libswresample.a libswscale/libswscale.a libavutil/libavutil.a -lavdevice -lavfilter -lavformat -lavcodec -lpostproc -lswresample -lswscale -lavutil -lass -lm -lharfbuzz -lfontconfig -lexpat -lfreetype -lexpat -lfribidi -lfreetype -lz -lpng12 -lz -lm -lva -lxcb -lXau -lXdmcp -lxcb-shm -lxcb -lXau -lXdmcp -lxcb-xfixes -lxcb-render -lxcb-shape -lxcb -lXau -lXdmcp -lxcb-shape -lxcb -lXau -lXdmcp -L/home/gaoxiang/project/crash-free-fix/benchmark/ffmpeg_deps/libs/lib -lx265 -lstdc++ -lm -lrt -ldl -lnuma -L/home/gaoxiang/project/crash-free-fix/benchmark/ffmpeg_deps/../ffmpeg_deps/libs/lib -lvpx -lm -lpthread -L/home/gaoxiang/project/crash-free-fix/benchmark/ffmpeg_deps/../ffmpeg_deps/libs/lib -lvpx -lm -lpthread -L/home/gaoxiang/project/crash-free-fix/benchmark/ffmpeg_deps/../ffmpeg_deps/libs/lib -lvpx -lm -lpthread -L/home/gaoxiang/project/crash-free-fix/benchmark/ffmpeg_deps/../ffmpeg_deps/libs/lib -lvpx -lm -lpthread -lvorbisenc -lvorbis -logg -ltheoraenc -ltheoradec -logg -L/home/gaoxiang/project/crash-free-fix/benchmark/ffmpeg_deps/../ffmpeg_deps/libs/lib -lopus -lm -L/home/gaoxiang/project/crash-free-fix/benchmark/ffmpeg_deps/../ffmpeg_deps/libs/lib -lopus -lm -lmp3lame -lfreetype -lz -lpng12 -lz -lm -L/home/gaoxiang/project/crash-free-fix/benchmark/ffmpeg_deps/../ffmpeg_deps/libs/lib -lfdk-aac -lm -lass -lm -lharfbuzz -lfontconfig -lexpat -lfreetype -lexpat -lfribidi -lfreetype -lz -lpng12 -lz -lm -lm -llzma -lbz2 -lz"

clang ${source} $PROJECT_CFLAGS $KLEE_CFLAGS -o ${target}
cd ..
