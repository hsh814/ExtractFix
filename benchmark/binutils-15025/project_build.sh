#!/bin/bash
compile_type=$1

subject=nm_new
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/klee
export LLVM_COMPILER=clang
make #-j32 &> /dev/null

cd binutils
make
$LOWFAT_CLANG -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-symbolize -lstlimpl -static-libstdc++ -static-libgcc -o nm-new nm.o bucomm.o version.o filemode.o ../bfd/libbfd.a ../libiberty/libiberty.a  ../zlib/libz.a

# copy target to root dir
cp binutils/${subject} ../

if [ $compile_type == 'to_bc' ];
then
    cd binutils
    extract-bc ${subject}

    cd ../..
    # copy target bc to root dir
    cp klee/tools/${subject}.bc .
fi

cd ..
