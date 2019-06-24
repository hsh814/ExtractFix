
git clone https://github.com/vadz/libtiff.git project
cd project
git checkout d9783e4
mkdir klee
cd klee
export LLVM_COMPILER=clang
CC=wllvm ../configure --disable-nls CFLAGS="-g -D__NO_STRING_INLINES  -D_FORTIFY_SOURCE=0 -U__OPTIMIZE__"
cd ..
