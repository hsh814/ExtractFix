#!/bin/bash

source=$1
target=$2

current_dir=`pwd`
cd project
clang ${source} -o ${target}
cd ..
