#!/bin/bash
compile_type=$1

subject=poc
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/klee
export LLVM_COMPILER=clang
make -j32  &> /dev/null

cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -I${current_dir}/project_specific_lib/ -lhook -L${current_dir}/project_specific_lib/ -Wno-everything"
if [ $compile_type == 'lowfat' ];
then
	compiler=${LOWFAT_CLANG}
	cflags="$cflags -fsanitize=signed-integer-overflow,unsigned-integer-overflow -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-reads -mllvm -lowfat-no-check-writes -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-check-whole-access -mllvm -lowfat-no-replace-globals -mllvm -lowfat-no-replace-alloca -mllvm -lowfat-no-replace-malloc -mllvm -lowfat-symbolize -lstlimpl"
	${compiler} ${cflags} -I../include/ -I./include -L.libs/ -lxml2 ../../poc.c -o poc
	# copy target to root dir
	cp ${subject} ../
fi



if [ $compile_type == 'to_bc' ];
then
	# get .o
	wllvm -g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -I/tmp/proj_work_dir_libxml2-1834_1564651092/project_specific_lib/ -lhook -L/tmp/proj_work_dir_libxml2-1834_1564651092/project_specific_lib/ -Wno-everything -I../include/ -I./include -c ../../poc.c
	# get exe
	wllvm -ggdb3 -Wall -W -o poc poc.o ./.libs/libxml2.a -I./include -L./.libs/ -lxml2 -lz -llzma -lm -ldl -lkleeRuntest -lkleeBasic -lhook -L/tmp/proj_work_dir_libxml2-1834_1564651092/project_specific_lib/ -Wl,-rpath
	# get .bc
	extract-bc -l /usr/local/bin/llvm-link poc

    cd ..
    # copy target bc to root dir
    cp klee/${subject}.bc .
    cp klee/${subject}.bc ../
else
	cd ../../
    $LOWFAT_CLANG -fsanitize=signed-integer-overflow,unsigned-integer-overflow -I./project/klee/include/ -I./project/include -L./project/klee/.libs/ -lxml2 -lstlimpl /home/nightwish/workspace/bug_repair/LowFat/lowfat.o poc.c -o poc
    cd ..
fi

cd ..
