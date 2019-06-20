#!/usr/bin/env python

#########################################################################
# This file is part of Fix2Fit.
# Copyright (C) 2016

# This is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
#         but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
###########################################################################


import subprocess
import os


def compile_llvm6(compile_command, work_dir, logger):
    CC = "clang"
    current_dir = os.path.dirname(os.path.realpath(__file__))
    klee_include = os.path.join(current_dir, "klee", "include")
    CFLAGS = "-I" + klee_include + " -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone"
    command = "CC="+CC+" CFLAGS=\'"+CFLAGS+"\' " + compile_command
    logger.debug("compile command: " + command)
    try:
        subprocess.check_output(command, cwd=work_dir, shell=True)
    except subprocess.CalledProcessError as e:
        logger.fatal("compile error, command line: " + command)

    logger.info("clang successfully compile project")


def run_mem2reg(work_dir, logger, binary_name):
    binary_full_path = os.path.join(work_dir, binary_name+".bc")
    command = "opt -mem2reg " + binary_full_path + " > " + binary_full_path
    logger.debug("mem2reg command: " + command)
    try:
        subprocess.check_output(command, cwd=work_dir, shell=True)
    except subprocess.CalledProcessError as e:
        logger.fatal("run mem2reg failed, command line: " + command)

    logger.info("successfully run mem2reg")

