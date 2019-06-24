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

import argparse
import coloredlogs, logging
import sys, time, os
# add the current path to PYTHONPATH
sys.path.append(os.path.dirname(os.path.realpath(__file__)))

import subprocess
from instrumentation import GSInserter, FuncTracer
from Global import BugType
from sanitizer import Sanitizer
from fault_localization import FaultLocalization
import runtime
import Global


def repair(source_path, binary_name, driver, test_list, bug_type, logger):
    work_dir = "/tmp/proj_work_dir_" + str(int(time.time()))
    logger.info("project working directory " + work_dir)
    subprocess.check_output(['cp', '-r', str(source_path), work_dir])
    runtime.project_config(work_dir, logger)
    project_path = os.path.join(work_dir, "project")

    crash_info = Global.CrashInfo("readSeparateTilesIntoBuffer", 994, {})

    if bug_type == 'buffer_overflow':
        # insert global variable for malloc, which is then used to generate crash-free-constraints
        GSInserter.insert_gs(project_path, project_path, logger)

        sanitizer = Sanitizer.BufferOverflowSanitizer(bug_type)
        crash_info = sanitizer.generate_crash_info()
        logger.debug("crash info: "+str(crash_info))

    # compile the program to bc file and optimize it using mem2reg
    runtime.compile_to_bc_llvm6(work_dir, logger)
    # runtime.run_mem2reg(work_dir, logger, binary_name)

    # instrument program by inserting function tracer
    func_tracer = FuncTracer.FuncTracer()
    bc_with_func_tracer = func_tracer.insert_function_trace(project_path, logger, binary_name)
    binary_name_with_func_tracer = runtime.compile_llvm6(work_dir, bc_with_func_tracer, logger)

    # run function tracer to generate function trace
    func_trace = runtime.run(work_dir, driver, binary_name_with_func_tracer, test_list, logger)
    func_list = process_func_trace(func_trace)
    # logger.debug("function trace" + str(func_list))

    # fault localization
    fl = FaultLocalization.FaultLocalization(work_dir, binary_name, func_list, crash_info, logger)
    potential_funcs = fl.get_potential_fault_locs()


def process_func_trace(func_trace):
    retval = []
    trace_list = func_trace.split('\n')[:-1]
    for trace in trace_list:
        retval.append(trace.split(' >>>> '))
    return retval


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Crash-Free-Fix')
    parser.add_argument('-s', '--source-path', dest='source_path', type=str, nargs=1,
                        help='the path of the project', required=True)

    parser.add_argument('-t', '--tests', dest='tests', type=str, nargs='+',
                        help='the test input', required=True)

    parser.add_argument('-c', '--run-command', dest='run_command', type=str, nargs=1,
                        help='the command to compile the target program', required=True)

    parser.add_argument('-b', '--bug-type', dest='bug_type', type=str, nargs=1,
                        help='the type of the crash/vulnerability(supported type: '+BugType.list()+')', required=True)

    parser.add_argument('-n', '--binary-name', dest='binary_name', type=str, nargs=1,
                        help='the binary name', required=False)

    parser.add_argument('-v', '--verbose', action='store_true', dest='verbose',
                        help='show debug information', required=False)

    args = parser.parse_args()

    # create logger
    if args.verbose:
        level = "DEBUG"
    else:
        level = "INFO"
    coloredlogs.install(level=level)
    logging.basicConfig()
    logger = logging.getLogger('Crash-free-fix ')

    if not args.source_path or not args.tests or not args.run_command:
        parser.print_help(sys.stderr)
        exit(1)

    test_list = args.tests
    bug_type = args.bug_type[0]
    if bug_type not in BugType.list():
        logger.fatal("Bug type" + bug_type + " is not supported.")
        parser.print_help(sys.stderr)
        exit(1)

    logger.debug("run crash-free-fix on project " + str(args.source_path))

    repair(args.source_path[0], args.binary_name[0], args.run_command[0], test_list, bug_type, logger)

