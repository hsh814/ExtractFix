#!/bin/bash
compile_type=$1

current_dir=`pwd`
# get project and set to corresponding version
#git clone https://github.com/vadz/libtiff.git project
cd project
#git checkout d9783e4


if ! grep -qF "size_t LOWFAT_GLOBAL_MS__readelf_get_data_423;" ./binutils/readelf.c;
then
	echo "PREPROCESS"
	sed -i '423s/malloc ((size_t) amt + 1)/malloc (({LOWFAT_GLOBAL_MS__readelf_get_data_423 = (size_t) amt + 1; LOWFAT_GLOBAL_MS__readelf_get_data_423;}))/' ./binutils/readelf.c
	sed -i '360isize_t LOWFAT_GLOBAL_MS__readelf_get_data_423;' ./binutils/readelf.c
fi


if ! grep -qF "extern size_t LOWFAT_GLOBAL_MS__readelf_get_data_423" ./binutils/dwarf.c;
then
	echo "PREPROCESS"
	sed -i '126iextern size_t LOWFAT_GLOBAL_MS__readelf_get_data_423;' ./binutils/dwarf.c
fi


# create build diretory and config
rm -rf klee
mkdir klee
cd klee

cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -Wno-everything"

if [ $compile_type == 'to_bc' ];
then
    # required by wllvm
    export LLVM_COMPILER=clang
    compiler=wllvm
elif [ $compile_type == 'lowfat' ];
then
    compiler=${LOWFAT_CLANG}
    cflags="$cflags -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-no-replace-globals -mllvm -lowfat-no-replace-alloca -mllvm -lowfat-symbolize -lstlimpl"
fi

CC=$compiler ../configure --enable-targets=all --disable-shared CFLAGS="$cflags"

cd ../..


