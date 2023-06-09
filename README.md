# crash-free-fix
Crash free program repair

## Requirement

1. LLVM-6.0: install LLVM-6.0 following the [instruction](https://llvm.org/docs/GettingStarted.html)
2. Boost, install it in ubuntu using the following command:
```
sudo apt-get install libboost-all-dev, pkg-config
```
3. Jsoncpp
```
sudo apt-get install libjsoncpp-dev
```
4. Python packages
```
pip install enum argparse coloredlogs
```

5. Experiment dependencies

**LibTiff**
To define ```JPEG_SUPPORT```  in the configuration:
```
sudo apt-get install libjpeg-dev libjbig-dev 
```

**Libjpeg**
```
sudo apt install nasm
```

**ffmpg**
```
sudo apt-get install libfreetype6-dev libva-dev libass-dev libavutil-dev
```

- export CFC_PROJ_ROOT=[YOUR-CFC-PROJ-ROOT] 

### Installation
1. Clone Crash-free-fix and its submodules
```
git clong --recursive https://github.com/gaoxiang9430/crash-free-fix.git
```
2. Compile klee
```
cd ExtractFix; cd src/klee
```

build Klee following the [instruction](https://klee.github.io/build-llvm60) and set the following enviornment variables

```
export PATH=$PATH:[YOUR-KLEE-PATH]/klee/build/bin
export LIBRARY_PATH=$LIBRARY_PATH:[YOUR-KLEE-PATH]/klee/build/lib
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:[YOUR-KLEE-PATH]/klee/build/lib
export C_INCLUDE_PATH=${C_INCLUDE_PATH}:[YOUR-KLEE-PATH]/klee/include
export CPLUS_INCLUDE_PATH=${CPLUS_INCLUDE_PATH}:[YOUR-KLEE-PATH]/klee/include
```
3. Compile sanitizer(LowFat) 
```
cd src/sanitizer/LowFat; ./build.sh
- export LIBRARY_PATH=$LIBRARY_PATH:[YOUR-LOWFAT-PATH]/llvm-4.0.0.src/projects/compiler-rt/lib/lowfat/
- export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:[YOUR-LOWFAT-PATH]/llvm-4.0.0.src/projects/compiler-rt/lib/lowfat/
```
4. Compile Crash-free-fix
```
- export LOWFAT_CLANG=[your-lowfat-clang-path]
- mkdir build; cd build; LLVM_HOME=[your-llvm-build-path] cmake ../src; make
```

