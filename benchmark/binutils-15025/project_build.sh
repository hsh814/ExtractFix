#!/bin/bash
compile_type=$1

subject=nm-new
current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

cd project/klee
export LLVM_COMPILER=clang
make -j32 #&> /dev/null

cd binutils
make nm-new #&> /dev/null

# copy target to root dir

if [ $compile_type == 'to_bc' ];
then
	cp ./${subject} ../..
    extract-bc ${subject}
    cd ../..
    # copy target bc to root dir
    cp klee/binutils/${subject}.bc .
    
else
	# build lowfat
	$LOWFAT_CLANG -W -Wall -Wstrict-prototypes -Wmissing-prototypes -Wshadow -Werror -I../../binutils/../zlib -g -D__NO_STRING_INLINES -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -Wno-everything -fsanitize=integer-divide-by-zero -fsanitize=lowfat -static-libstdc++ -static-libgcc -o nm-new nm.o bucomm.o version.o filemode.o  ../bfd/.libs/libbfd.a -L${current_dir}/project/klee/zlib -lkleeRuntest -lkleeBasic -lstlimpl -lz ../libiberty/libiberty.a
	cp ./${subject} ../..
fi

cd ${current_dir}