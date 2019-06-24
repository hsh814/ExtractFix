source=$1
target=$2

cd project
clang ${source} -llzma -lz -lm -ljpeg -ljbig -Wl,-rpath -o ${target}
cd ..
