
#git clone https://github.com/vadz/libtiff.git project
current_dir=`pwd`
cd project
#git checkout d9783e4
mkdir klee
cd klee
export LLVM_COMPILER=clang
CC=wllvm ../configure --disable-nls CFLAGS="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__ -I${current_dir}/project_specific_lib/ -lhook -L${current_dir}/project_specific_lib/" &> /dev/null
cd ..
