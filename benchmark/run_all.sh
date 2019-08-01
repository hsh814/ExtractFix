#!/bin/bash

./main.py -s ../benchmark/libtiff-5321 -t test_case -c driver -b buffer_overflow -n tiffcrop -v
./main.py -s ../benchmark/libtiff-8128 -t test_case -c driver -b buffer_overflow -n thumbnail -v
./main.py -s ../benchmark/libtiff-3186 -t test_case -c driver -b api_specific -n gif2tiff -v
./main.py -s ../benchmark/libtiff-10094/ -t test_case -c driver -b buffer_overflow -n tiff2pdf -v
./main.py -s ../benchmark/libtiff-2611 -t test_case -c driver -b divide_by_0 -n tiffmedian -v
