#!/bin/bash

# libtiff
./main.py -s ../benchmark/libtiff-5321 -t test_case -c driver -b buffer_overflow -n tiffcrop -v
./main.py -s ../benchmark/libtiff-8128 -t test_case -c driver -b buffer_overflow -n thumbnail -v
./main.py -s ../benchmark/libtiff-3186 -t test_case -c driver -b api_specific -n gif2tiff -v
./main.py -s ../benchmark/libtiff-5314 -t test_case -c driver -b buffer_overflow -n rgb2ycbcr -v
./main.py -s ../benchmark/libtiff-9273 -t test_case -c driver -b buffer_overflow -n tiffsplit -v
./main.py -s ../benchmark/libtiff-2633 -t test_case -c driver -b buffer_overflow -n tiff2ps -v
./main.py -s ../benchmark/libtiff-10094 -t test_case -c driver -b buffer_overflow -n tiff2pdf -v
./main.py -s ../benchmark/libtiff-2611 -t test_case -c driver -b divide_by_0 -n tiffmedian -v

# Coreutil
./main.py -s ../benchmark/coreutils-26545 -t test_case -c driver -b buffer_overflow -n shred -v
./main.py -s ../benchmark/coreutils-25003 -t test_case -c driver -b api_specific -n split -v
./main.py -s ../benchmark/coreutils-25023 -t test_case -c driver -b buffer_overflow -n echo -v
./main.py -s ../benchmark/coreutils-19784 -t test_case -c driver -b buffer_overflow -n make-prime-list -v
