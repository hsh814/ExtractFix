#!/bin/bash
compile_type=$1

subject=tools/target_dec_dfa_fuzzer
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project
export LLVM_COMPILER=clang
make clean
make -j32  &> /dev/null
make ${subject}

# copy target to root dir
cp ${subject} ./

TEMP_PATH=/home/nightwish/workspace/bug_repair/crash-free-fix/benchmark/ffmpeg_deps

if [ $compile_type == 'to_bc' ];
then
    KLEE_CFLAGS="-lkleeRuntest -lkleeBasic -lhook -L${current_dir}/project_specific_lib/"
    PROJECT_CFALGS="-std=c++11 -Llibavcodec -Llibavdevice -Llibavfilter -Llibavformat -Llibavresample -Llibavutil -Llibpostproc -Llibswscale -Llibswresample -L${TEMP_PATH}/libs/lib  -Wl,--as-needed -Wl,-z,noexecstack -Wl,--warn-common -Wl,-rpath-link=libpostproc:libswresample:libswscale:libavfilter:libavdevice:libavformat:libavcodec:libavutil:libavresample -Qunused-arguments   libavdevice/libavdevice.a libavfilter/libavfilter.a libavformat/libavformat.a libavcodec/libavcodec.a libpostproc/libpostproc.a libswresample/libswresample.a libswscale/libswscale.a libavutil/libavutil.a -lavdevice -lavfilter -lavformat -lavcodec -lpostproc -lswresample -lswscale -lavutil -lass -lm -lharfbuzz -lfontconfig -lexpat -lfreetype -lexpat -lfribidi -lfreetype -lz -lpng12 -lz -lm -lva -lxcb -lXau -lXdmcp -lxcb -lXau -lXdmcp -lxcb-xfixes -lxcb-render -lxcb-shape -lxcb -lXau -lXdmcp -lxcb-shape -lxcb -lXau -lXdmcp -L ${TEMP_PATH}libs/lib -lstdc++ -lm -lrt -ldl -lnuma -L ${TEMP_PATH}../ffmpeg_deps/libs/lib -lvpx -lm -lpthread -L ${TEMP_PATH}../ffmpeg_deps/libs/lib -lvpx -lm -lpthread -L ${TEMP_PATH}../ffmpeg_deps/libs/lib -lvpx -lm -lpthread -L ${TEMP_PATH}../ffmpeg_deps/libs/lib -lvpx -lm -lpthread -lvorbisenc -lvorbis -logg -ltheoraenc -ltheoradec -logg -L ${TEMP_PATH}../ffmpeg_deps/libs/lib -lopus -lm -L ${TEMP_PATH}../ffmpeg_deps/libs/lib -lopus -lm -lmp3lame -lfreetype -lz -lpng12 -lz -lm -L ${TEMP_PATH}../ffmpeg_deps/libs/lib -lfdk-aac -lm -lass -lm -lharfbuzz -lfontconfig -lexpat -lfreetype -lexpat -lfribidi -lfreetype -lz -lpng12 -lz -lm -lm -llzma -lz"
    make ${subject}
    wllvm -ggdb3 -Wall -W -o tools/target_dec_dfa_fuzzer tools/target_dec_dfa_fuzzer.o afl_driver.o ${PROJECT_CFALGS} ${KLEE_CFLAGS} -Wl,-rpath
    extract-bc -l /usr/local/bin/llvm-link ${subject}
    # copy target bc to root dir
    cp ${subject}.bc .
fi

cd ..

