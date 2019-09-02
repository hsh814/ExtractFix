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


def project_config(work_dir, logger, build_type="to_bc"):
    command = "./project_config.sh " + build_type + " &> /dev/null"
    logger.debug("compile command: " + command)
    try:
        subprocess.check_output(command, cwd=work_dir, shell=True)
    except subprocess.CalledProcessError as e:
        logger.fatal("config error, command line: " + command)
        exit(1)

    logger.info("successfully config project")


def project_build(work_dir, logger, build_type="to_bc"):
    # current_dir = os.path.dirname(os.path.realpath(__file__))
    # klee_include = os.path.join(current_dir, "klee", "include")
    # CFLAGS = "-I" + klee_include + " -emit-llvm -c -g -O0 -Xclang -disable-O0-optnone"
    # command = "CC="+CC+" CFLAGS=\'"+CFLAGS+"\' " + compile_command
    command = "./project_build.sh " + build_type + " &> /dev/null"
    logger.debug("compile command: " + command)
    try:
        subprocess.check_output(command, cwd=work_dir, shell=True)
    except subprocess.CalledProcessError as e:
        logger.fatal("compile error, command line: " + command)
        exit(1)

    logger.info("clang successfully generate bc file")


def run_mem2reg(work_dir, logger, binary_name):
    binary_full_path = os.path.join(work_dir, binary_name+".bc")
    command = "opt -S -mem2reg " + binary_full_path + " > " + binary_full_path+".ll"
    command2 = "llvm-as " + binary_full_path+".ll" + " -o " + binary_full_path
    logger.debug("mem2reg command: " + command)
    try:
        subprocess.check_output(command, cwd=work_dir, shell=True)
        subprocess.check_output(command2, cwd=work_dir, shell=True)
    except subprocess.CalledProcessError as e:
        logger.fatal("run mem2reg failed, command line: " + command)
        exit(1)

    logger.info("successfully run mem2reg")


def compile_llvm6(work_dir, binary_name, logger):
    command = "./project_compile.sh " + binary_name + ".bc " + binary_name + " > /dev/null"
    logger.debug("compile command: " + command)
    try:
        subprocess.check_output(command, cwd=work_dir, shell=True)
    except subprocess.CalledProcessError as e:
        logger.fatal("compile error, command line: " + command)
        exit(1)

    logger.info("clang successfully compile project")

    return binary_name


def run(work_dir, driver, binary_full_path, test_list, logger):
    # TODO: assume the first test is the failing test
    command = "./" + driver + " " + binary_full_path + " " + test_list[0] + " > /tmp/run_info2 2> /tmp/run_info"
    logger.debug("run command: " + command)
    try:
        result = subprocess.check_output(command, cwd=work_dir, shell=True)
    except subprocess.CalledProcessError as e:
        logger.fatal("run " + command + " failed")

    logger.info("successfully run " + command)

    return result


def run_klee(work_dir, driver, binary_full_path, test_list, crash_info, logger, fix_loc=None):
    crash_loc = crash_info.file_name + ":" + str(crash_info.line_no)
    fix_loc_str = fix_loc.get_file_name() + ":" + str(fix_loc.get_line_no() + 1)
    command = "./klee-" + driver + " " + binary_full_path + " " + test_list[0] + " " + crash_loc + " " + fix_loc_str+ " 2> /dev/null"
    logger.debug("run command: " + command)
    try:
        result = subprocess.check_output(command, cwd=work_dir, shell=True)
    except subprocess.CalledProcessError as e:
        logger.fatal("run " + command + " failed")
        exit(1)

    logger.info("successfully run " + command)

    return result

