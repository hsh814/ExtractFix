
subject=tiffcrop

current_dir=`pwd`

export LLVM_COMPILER=clang
cd project

cd klee
make -j32

cd tools
wllvm -ggdb3 -Wall -W -o ${subject} ${subject}.o ../libtiff/.libs/libtiff.a ../port/.libs/libport.a -llzma -lz -lm -ljpeg -ljbig -lhook -L${current_dir}/project_specific_lib/ -Wl,-rpath
extract-bc -l /usr/local/bin/llvm-link ${subject}
cd ..

cd ..

cp klee/tools/tiffcrop.bc .
cd ..
