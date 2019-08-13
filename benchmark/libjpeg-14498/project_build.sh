#!/bin/bash
compile_type=$1

subject=cjpeg
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/klee
export LLVM_COMPILER=clang
make -j32 &> /dev/null

# copy target to root dir
cp $subject ../

if [ $compile_type == 'to_bc' ];
then
    KLEE_CFLAGS="-lkleeRuntest -lkleeBasic -lhook -L${current_dir}/project_specific_lib/"
    PROJECT_CFALGS="./libjpeg.a -ljpeg ./libturbojpeg.a -lturbojpeg -llzma -lz -lm -ljbig"
    wllvm -ggdb3 -Wall -W -o ${subject} CMakeFiles/cjpeg-static.dir/cjpeg.c.o CMakeFiles/cjpeg-static.dir/cdjpeg.c.o CMakeFiles/cjpeg-static.dir/rdgif.c.o CMakeFiles/cjpeg-static.dir/rdppm.c.o CMakeFiles/cjpeg-static.dir/rdswitch.c.o CMakeFiles/cjpeg-static.dir/rdbmp.c.o CMakeFiles/cjpeg-static.dir/rdtarga.c.o ${PROJECT_CFALGS} ${KLEE_CFLAGS} -Wl,-rpath
    extract-bc -l /usr/local/bin/llvm-link ${subject}

    cd ..
    # copy target bc to root dir
    cp klee/${subject}.bc .
fi

cd ..
