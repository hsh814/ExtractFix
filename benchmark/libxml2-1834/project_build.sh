#!/bin/bash
compile_type=$1

subject=poc
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/klee
export LLVM_COMPILER=clang
make -j32 # &> /dev/null

if [ $compile_type == 'lowfat' ];
then
	cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -I${current_dir}/project_specific_lib/ -lhook -L${current_dir}/project_specific_lib/ -Wno-everything"

	compiler=${LOWFAT_CLANG}
	cflags="$cflags -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-symbolize -lstlimpl"
	${compiler} ${cflags} -I../include/ -I./include -L.libs/ -lxml2 ../../poc.c -o poc
fi

# copy target to root dir
cp ${subject} ../

if [ $compile_type == 'to_bc' ];
then
    cd tools
    KLEE_CFLAGS="-lkleeRuntest -lkleeBasic -lhook -L${current_dir}/project_specific_lib/"
    PROJECT_CFALGS="./.libs/libxml2.a -I./include -L./.lib/ -lxml2 -lz -llzma -lm -ldl"
    wllvm -ggdb3 -Wall -W -o ${subject} ${subject}.o ${PROJECT_CFALGS} ${KLEE_CFLAGS} -Wl,-rpath
    extract-bc -l /usr/local/bin/llvm-link ${subject}

    cd ../..
    # copy target bc to root dir
    cp klee/${subject}.bc .
fi

cd ..
