# crash-free-fix
Crash free program repair

## Requirement

1. LLVM-6.0: install LLVM-6.0 following the [instruction](https://llvm.org/docs/GettingStarted.html)
2. Boost, install it in ubuntu using the following command:
```
sudo apt-get install libboost-all-dev
```
3. Jsoncpp
```
sudo apt-get install libjsoncpp-dev
```
4. Python packages
```
pip install pycparser enum argparse coloredlogs
```

### Installation
1. Clone Crash-free-fix and its submodules
```
git clong --recursive https://github.com/gaoxiang9430/crash-free-fix.git
```
2. Compile klee
```
make; make install or set the following enviornment variables
	export PATH=$PATH:[YOUR-KLEE-PATH]/klee/build/bin
	export LIBRARY_PATH=$LIBRARY_PATH:[YOUR-KLEE-PATH]/klee/build/lib
	export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:[YOUR-KLEE-PATH]/klee/build/lib
	export C_INCLUDE_PATH=${C_INCLUDE_PATH}:[YOUR-KLEE-PATH]/klee/include
	export CPLUS_INCLUDE_PATH=${CPLUS_INCLUDE_PATH}:[YOUR-KLEE-PATH]/klee/include
```
3. Compile sanitizer(LowFat) 
```
cd src/sanitizer/LowFat; ./build.sh
	export LIBRARY_PATH=$LIBRARY_PATH:[YOUR-LOWFAT-PATH]/llvm-4.0.0.src/projects/compiler-rt/lib/lowfat/
	export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:[YOUR-LOWFAT-PATH]/llvm-4.0.0.src/projects/compiler-rt/lib/lowfat/
```
4. Compile Crash-free-fix
```
mkdir build; cd build; LLVM_HOME=[your-llvm-build-path] cmake ../src; make
```

