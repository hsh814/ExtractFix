export PATH=/ExtractFix/src/klee/build/bin:$PATH
export LIBRARY_PATH=$LIBRARY_PATH:/ExtractFix/src/klee/build/lib
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/ExtractFix/src/klee/build/lib
export C_INCLUDE_PATH=${C_INCLUDE_PATH}:/ExtractFix/src/klee/include
export CPLUS_INCLUDE_PATH=${CPLUS_INCLUDE_PATH}:/ExtractFix/src/klee/include

export LIBRARY_PATH=$LIBRARY_PATH:/ExtractFix/src/sanitizer/LowFat/llvm-4.0.0.src/projects/compiler-rt/lib/lowfat/
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/ExtractFix/src/sanitizer/LowFat/llvm-4.0.0.src/projects/compiler-rt/lib/lowfat/

export LOWFAT_CLANG=/ExtractFix/src/sanitizer/LowFat/build/bin/clang
export LLVM_HOME=/usr/bin
