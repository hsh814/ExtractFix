#!/bin/bash

# libtiff
./ExtractFix.py -s ../benchmark/libtiff-5321 -t test_case -c driver -b buffer_overflow -n tiffcrop -v
./ExtractFix.py -s ../benchmark/libtiff-8128 -t test_case -c driver -b buffer_overflow -n thumbnail -v
./ExtractFix.py -s ../benchmark/libtiff-3186 -t test_case -c driver -b api_specific -n gif2tiff -v
./ExtractFix.py -s ../benchmark/libtiff-5314 -t test_case -c driver -b buffer_overflow -n rgb2ycbcr -v
./ExtractFix.py -s ../benchmark/libtiff-9273 -t test_case -c driver -b buffer_overflow -n tiffsplit -v
./ExtractFix.py -s ../benchmark/libtiff-10269 -t test_case -c driver -b buffer_overflow -n tiffcp -v
./ExtractFix.py -s ../benchmark/libtiff-2633 -t test_case -c driver -b buffer_overflow -n tiff2ps -v
./ExtractFix.py -s ../benchmark/libtiff-10094 -t test_case -c driver -b buffer_overflow -n tiff2pdf -v

./ExtractFix.py -s ../benchmark/libtiff-3623 -t test_case -c driver -b divide_by_0 -n rgb2ycbcr -v
./ExtractFix.py -s ../benchmark/libtiff-7595 -t test_case -c driver -b divide_by_0 -n tiffcp -v
./ExtractFix.py -s ../benchmark/libtiff-2611 -t test_case -c driver -b divide_by_0 -n tiffmedian -v

# Binutils
./ExtractFix.py -s ../benchmark/binutils-10372/ -t test_case -c driver -b buffer_overflow -n readelf -v

# libxml2
./ExtractFix.py -s ../benchmark/libxml2-1834/ -t test_case -c driver -b buffer_overflow -n poc -v
./ExtractFix.py -s ../benchmark/libxml2-1839/ -t test_case -c driver -b buffer_overflow -n xmllint -v
./ExtractFix.py -s ../benchmark/libxml2-1838/ -t test_case -c driver -b buffer_overflow -n xmllint -v
./ExtractFix.py -s ../benchmark/libxml2-5134/ -t test_case -c driver -b buffer_overflow -n xmllint -v

# libjpeg
./ExtractFix.py -s ../benchmark/libjpeg-14498 -t test_case -c driver -b buffer_overflow -n cjpeg -v
./ExtractFix.py -s ../benchmark/libjpeg-19664 -t test_case -c driver -b buffer_overflow -n djpeg -v

# Coreutil
./ExtractFix.py -s ../benchmark/coreutils-26545 -t test_case -c driver -b buffer_overflow -n shred -v
./ExtractFix.py -s ../benchmark/coreutils-25003 -t test_case -c driver -b api_specific -n split -v
./ExtractFix.py -s ../benchmark/coreutils-25023 -t test_case -c driver -b buffer_overflow -n echo -v
./ExtractFix.py -s ../benchmark/coreutils-19784 -t test_case -c driver -b buffer_overflow -n make-prime-list -v

# Jasper
./ExtractFix.py -s ../benchmark/jasper-8691 -t test_case -c driver -b divide_by_0 -n imginfo -v
./ExtractFix.py -s ../benchmark/jasper-8692 -t test_case -c driver -b divide_by_0 -n imginfo -v
./ExtractFix.py -s ../benchmark/jasper-9387 -t test_case -c driver -b integer_overflow -n imginfo -v
