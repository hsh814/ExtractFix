#!/bin/bash

# libtiff
./main.py -s ../benchmark/libtiff-5321 -t test_case -c driver -b buffer_overflow -n tiffcrop -v
./main.py -s ../benchmark/libtiff-8128 -t test_case -c driver -b buffer_overflow -n thumbnail -v
./main.py -s ../benchmark/libtiff-3186 -t test_case -c driver -b api_specific -n gif2tiff -v
./main.py -s ../benchmark/libtiff-5314 -t test_case -c driver -b buffer_overflow -n rgb2ycbcr -v
./main.py -s ../benchmark/libtiff-9273 -t test_case -c driver -b buffer_overflow -n tiffsplit -v
./main.py -s ../benchmark/libtiff-10269 -t test_case -c driver -b buffer_overflow -n tiffcp -v
./main.py -s ../benchmark/libtiff-2633 -t test_case -c driver -b buffer_overflow -n tiff2ps -v
./main.py -s ../benchmark/libtiff-10094 -t test_case -c driver -b buffer_overflow -n tiff2pdf -v

./main.py -s ../benchmark/libtiff-3623 -t test_case -c driver -b divide_by_0 -n rgb2ycbcr -v
./main.py -s ../benchmark/libtiff-7595 -t test_case -c driver -b divide_by_0 -n tiffcp -v
./main.py -s ../benchmark/libtiff-2611 -t test_case -c driver -b divide_by_0 -n tiffmedian -v

# Binutils
./main.py -s ../benchmark/binutils-10372/ -t test_case -c driver -b buffer_overflow -n readelf -v

# libxml2
./main.py -s ../benchmark/libxml2-1834/ -t test_case -c driver -b buffer_overflow -n poc -v
./main.py -s ../benchmark/libxml2-1839/ -t test_case -c driver -b buffer_overflow -n xmllint -v
./main.py -s ../benchmark/libxml2-1838/ -t test_case -c driver -b buffer_overflow -n xmllint -v
./main.py -s ../benchmark/libxml2-5134/ -t test_case -c driver -b buffer_overflow -n xmllint -v

# libjpeg
./main.py -s ../benchmark/libjpeg-14498 -t test_case -c driver -b buffer_overflow -n cjpeg -v
./main.py -s ../benchmark/libjpeg-19664 -t test_case -c driver -b buffer_overflow -n djpeg -v

# Coreutil
./main.py -s ../benchmark/coreutils-26545 -t test_case -c driver -b buffer_overflow -n shred -v
./main.py -s ../benchmark/coreutils-25003 -t test_case -c driver -b api_specific -n split -v
./main.py -s ../benchmark/coreutils-25023 -t test_case -c driver -b buffer_overflow -n echo -v
./main.py -s ../benchmark/coreutils-19784 -t test_case -c driver -b buffer_overflow -n make-prime-list -v
