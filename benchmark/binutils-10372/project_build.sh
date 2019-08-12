#!/bin/bash
compile_type=$1

current_dir="$( cd "$(dirname "$0")" ; pwd -P )"

subject=readelf

cd project/klee
export LLVM_COMPILER=clang
make -j32 #&> /dev/null

cd binutils
make readelf #&> /dev/null


# copy target to root dir
#cp binutils/${subject} ../

if [ $compile_type == 'to_bc' ];
then
    wllvm -W -Wall -Wstrict-prototypes -Wmissing-prototypes -Wshadow -Werror -I../../binutils/../zlib -g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -Wno-everything -static-libstdc++ -static-libgcc  -o readelf readelf.o version.o unwind-ia64.o dwarf.o elfcomm.o  ../libiberty/libiberty.a -L./../zlib -lz
    extract-bc -l /usr/local/bin/llvm-link readelf
    # copy target bc to root dir
    cp ./${subject}.bc ../../
else    
    # build lowfat
	$LOWFAT_CLANG -W -Wall -Wstrict-prototypes -Wmissing-prototypes -Wshadow -Werror -I../../binutils/../zlib -g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -Wno-everything -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-symbolize -lstlimpl  -static-libstdc++ -static-libgcc  -o readelf readelf.o version.o unwind-ia64.o dwarf.o elfcomm.o  ../libiberty/libiberty.a -L./../zlib -lz
	cp ./readelf ../..
fi


