source=$1
target=$2

current_dir=`pwd`
cd project
clang ${source} -llzma -lz -lm -ljpeg -ljbig -lhook -L${current_dir}/project_specific_lib/ -Wl,-rpath -o ${target}
cd ..
