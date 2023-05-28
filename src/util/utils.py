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

import os
import subprocess
from instrumentation.instrumentation_utils import get_import_head_folders

system_header = os.environ['C_INCLUDE_PATH'].split(":")
system_header.append('/usr/local/lib/clang/6.0.1/include')
cur_dir = os.path.dirname(os.path.abspath(__file__))

def read_fix_line(project_path, file_path, line_no):
    full_path = os.path.join(project_path, file_path)
    with open(full_path) as f:
        contents = f.readlines()
        return contents[line_no]


def process_func_trace(func_trace, crash_info):
    retval = []
    trace_list = [item[:-1] for item in func_trace]
    start = False
    for trace in trace_list:
        if "main" in trace:
            start = True
        if not start:
            continue
        if ' >>>> ' not in trace:
            continue
        entry = trace.split(' >>>> ')
        if entry[0] != "IN" and entry[0] != "OUT":
            continue

        if entry[0] == "IN" and entry[1] == crash_info.get_function_name():
            retval.append(entry)
            break
        retval.append(entry)
    return retval


def apply_path(logger, project_path, source_path, file_path, line_no, patch, patch_path, operation="replace"):
    origin_file = os.path.join(project_path, file_path)
    with open(origin_file, 'r') as f:
        contents = f.readlines()
    if operation == "replace":
        contents[line_no] = patch + "\n"
    elif operation == "insert":
        contents.insert(line_no, patch + "\n")

    print ("patch is: " + patch)

    patched_file = origin_file+"_fixed.c"
    with open(patched_file, 'w') as f:
        for item in contents:
            f.write(item)
    logger.info("Successfully apply the patch")

    origin_file = os.path.join(source_path, "project", file_path)
    command = "diff " + origin_file + " " + patched_file + " > " + patch_path
    logger.debug("compile command: " + command)
    try:
        subprocess.check_output(command, shell=True)
    except subprocess.CalledProcessError as e:
        logger.info("successfully generate patch: " + patch_path)


def infer_return_value(project_dir, function_name, crash_file, logger):
    include_options = get_import_head_folders(project_dir, system_header)
    tail = ' '.join(include_options)
    crash_file = os.path.join(project_dir, crash_file)
    ret_infer = os.path.join(cur_dir, "RetInfer")
    command = ret_infer + " " + crash_file + \
              " -fun_name " + function_name + \
              " -- " + tail + \
              " 2> /dev/null"

    logger.debug("insert klee assume command: " + command)
    ret = "-1"

    try:
        ret = subprocess.check_output(command, cwd=project_dir, shell=True)
    except subprocess.CalledProcessError as e:
        logger.fatal("error, command line: " + command)
        exit(1)

    # logger.debug("return type is : " + str(ret))
    return __infer_return_value(ret)


def __infer_return_value(ret):
    pairs = ret.split("\n")
    ret_type = 'int'
    for pair in pairs:
        key, value = pair.split(":")
        if key == "constant" and value != "":
            return value
        elif key == "retType":
            ret_type = value
    if ret_type == 'int':
        return '0'
    elif ret_type == 'bool':
        return 'false'
    else:
        return "NULL"
