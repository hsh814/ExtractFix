#!/bin/bash
compile_type=$1

current_dir=`pwd`
# get project and set to corresponding version
#git clone https://github.com/vadz/libtiff.git project
cd project
#git checkout d9783e4

sed -i '2901s/_TIFFmemcpy(buffer, jpt, count - 2)/\/\/_TIFFmemcpy(buffer, jpt, count - 2);/' tools/tiff2pdf.c
sed -i '2904s/table_end\[0\] = buffer\[bufferoffset-2\]/table_end[1]=buffer[bufferoffset-1]/' tools/tiff2pdf.c
sed -i '2905s/table_end\[1\] = buffer\[bufferoffset-1\];/table_end[0]=buffer[bufferoffset-2];/' tools/tiff2pdf.c

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

CC=$compiler ../configure --disable-nls CFLAGS="$cflags"

cd ../..


