#!/bin/bash

work_dir=$(pwd)
git clone https://github.com/llvm/llvm-project.git llvm6
pushd llvm6
git checkout llvmorg-6.0.1

mkdir build
cmake -G "Unix Makefiles" -DLLVM_ENABLE_PROJECTS='clang;clang-tools-extra;libcxx;libcxxabi;libunwind;compiler-rt;polly' -DCMAKE_BUILD_TYPE=Release ../llvm
make -j2
make install
popd

