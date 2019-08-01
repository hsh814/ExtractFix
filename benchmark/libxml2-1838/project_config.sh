#!/bin/bash
compile_type=$1

current_dir=`pwd`
# get project and set to corresponding version
# git clone https://gitlab.gnome.org/GNOME/libxml2/ project
cd project
#git checkout d9783e4

# create build diretory and config
rm -rf klee
mkdir klee
cd klee

sed -i 's/#define FQUOTIENT(a,b)                  (floor(((double)a\/(double)b)))/double FQUOTIENT(double a, double b){return floor(((double)a\/(double)b));}/' ../xmlschemastypes.c
sed -i 's/xmlMalloc/malloc/g' ../parserInternals.c
sed -i 's/xmlMallocAtomic/malloc/g' ../parserInternals.c
sed -i 's/xmlRealloc/realloc/g' ../parserInternals.c

sed -i 's/xmlMalloc/malloc/g' ../xmlIO.c
sed -i 's/xmlMallocAtomic/malloc/g' ../xmlIO.c
sed -i 's/xmlRealloc/realloc/g' ../xmlIO.c

sed -i 's/xmlRealloc/realloc/g' ../parser.c
sed -i 's/xmlMallocAtomic/malloc/g' ../parser.c
sed -i 's/xmlMalloc/malloc/g' ../parser.c

# ../parserInternals.c:1351

cflags="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -lkleeRuntest -lkleeBasic -I${current_dir}/project_specific_lib/ -lhook -L${current_dir}/project_specific_lib/ -Wno-everything"

if [ $compile_type == 'to_bc' ];
then
    # required by wllvm
    export LLVM_COMPILER=clang
    compiler=wllvm
elif [ $compile_type == 'lowfat' ];
then
    compiler=${LOWFAT_CLANG}
    cflags="$cflags -fsanitize=lowfat -mllvm -lowfat-debug -mllvm -lowfat-no-check-memset -mllvm -lowfat-no-check-memcpy -mllvm -lowfat-no-check-escapes -mllvm -lowfat-no-check-fields -mllvm -lowfat-no-replace-globals -mllvm -lowfat-symbolize -lstlimpl"
fi

CC=$compiler CFLAGS="$cflags" ../autogen.sh --enable-static --without-threads --without-thread-alloc --with-threads=no --with-thread-alloc=no

cd ../..


