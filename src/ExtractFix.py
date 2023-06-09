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
import sys, time, os, ntpath, time
# add the current path to PYTHONPATH
full_path = os.path.dirname(os.path.realpath(__file__))
sys.path.append(full_path)
import subprocess
from instrumentation import ProjPreprocessor, FuncTracer, SymVarInserter
from Global import BugType
from sanitizer import Sanitizer
from fault_localization import FaultLocalization
import runtime
import Global
from util import utils


def clear_log():
    command = "rm -rf /tmp/run_info /tmp/callee.txt /tmp/fixlocations.json /tmp/callee.txt /tmp/cfc.out"
    subprocess.call(command, cwd="/tmp", shell=True)


def save_log(source_path, file_path, logs):
    log_path = os.path.join(source_path, logs)

    if not os.path.isdir(log_path):
        command = "mkdir " + log_path
        subprocess.call(command, shell=True)

    command = "mv " + " " + file_path + " " + log_path
    logger.debug("saving log " + command)
    subprocess.call(command, shell=True)
    logger.debug("logs are save to directory " + log_path)


def path_leaf(path):
    head, tail = ntpath.split(path)
    return tail or ntpath.basename(head)


def repair(source_path, binary_name, driver, test_list, bug_type, logger):
    start_time = time.time()
    index = 0

    clear_log()  # clear the log of last run
    proj_name = path_leaf(source_path)
    work_dir = "/tmp/proj_work_dir_" + proj_name + "_" + str(int(time.time()))
    logger.info("project working directory " + work_dir)
    subprocess.check_output(['cp', '-r', str(source_path), work_dir])
    project_path = os.path.join(work_dir, "project")

    if bug_type == 'buffer_overflow' or bug_type == 'integer_overflow' or bug_type == 'divide_by_0':
        runtime.project_config(work_dir, logger, "to_bc")
        ProjPreprocessor.__preprocess(project_path, lib=True, logger=logger)

        if bug_type == 'buffer_overflow':
            # insert global variable for malloc, which is then used to generate crash-free-constraints
            ProjPreprocessor.__preprocess(project_path, globalize=True, logger=logger)

        sanitizer = Sanitizer.BufferOverflowSanitizer(work_dir, project_path, binary_name, driver, test_list, logger)
        # TODO: implement crash info generation
        crash_info = sanitizer.generate_crash_info()
        logger.info("crash info: "+str(crash_info))

    elif bug_type == 'api_specific':
        # TODO: remove
        if "libtiff-3186" in source_path:
            crash_info = Global.CrashInfo("tools", "gif2tiff.c", "readextension", 354, "count>=0")  # 3186
        elif "coreutils-25003" in source_path:
            crash_info = Global.CrashInfo("src", "split.c", "bytes_chunk_extract", 987, "initial_read - start>=0")  # 25003
        else:
            logger.fatal("unsupported api misuse case")
            exit(1)
        logger.info("crash info: "+str(crash_info))

    save_log(source_path, "/tmp/cfc.out", "logs")

    runtime.project_config(work_dir, logger, "to_bc")
    # compile the program to bc file and optimize it using mem2reg
    runtime.project_build(work_dir, logger, "to_bc")
    # runtime.run_mem2reg(work_dir, logger, binary_name)
    logger.info("successfully generate bc file: " + project_path + "/" + binary_name + ".bc")

    # instrument program by inserting function tracer
    func_tracer = FuncTracer.FuncTracer()
    bc_full_path_with_func_tracer = func_tracer.insert_function_trace(project_path, logger, binary_name)
    binary_full_path_with_func_tracer = runtime.compile_llvm6(work_dir, bc_full_path_with_func_tracer, logger)

    # run function tracer to generate function trace
    runtime.run(work_dir, driver, binary_full_path_with_func_tracer, test_list, logger)
    func_trace = open("/tmp/run_info", 'r').readlines()
    func_list = utils.process_func_trace(func_trace, crash_info)
    logger.debug("the length of function trace" + str(len(func_list)))

    save_log(source_path, "/tmp/callee.txt", "logs")
    save_log(source_path, "/tmp/run_info", "logs")

    # fault localization
    fl = FaultLocalization.FaultLocalization(project_path, binary_name, func_list, crash_info, logger)
    potential_fixes = fl.get_potential_fault_locs()
    logger.info("successfully generate potential fix location: " + "/tmp/fixlocations.json")

    save_log(source_path, "/tmp/fixlocations.json", "logs")

    if len(potential_fixes) == 0:
        logger.info("directly apply patch")
        log_path = os.path.join(source_path, "result"+str(index))
        if not os.path.isdir(log_path):
            command = "mkdir " + log_path
            subprocess.call(command, shell=True)
        patch_path = os.path.join(log_path, "patch")
        # TODO: negate constraint and add return statement
        ret = utils.infer_return_value(project_path, crash_info.get_function_name(),
                                       crash_info.get_refined_name(), logger)
        patch = "if("+crash_info.get_cfc()+") return " + ret + ";"
        utils.apply_path(logger, project_path, source_path, crash_info.get_refined_name(),
                         crash_info.get_line_no()-1, patch, patch_path, "insert")
        logger.info("execution time (in minutes) is: " + str(time.time()-start_time))
        exit(0)

    # adjust line number because of include<klee/klee.h> injection in the following instrumentation

    crash_info.line_no += 2
    for fix_loc in potential_fixes:
        sym_var_inserter = SymVarInserter.SymVarInserter(project_path, logger, crash_info)
        # insert symbolic variables at source code level
        sym_var_inserter.insert_sym_vars(fix_loc)
        # compile the program to bc file
        runtime.project_build(work_dir, logger, "to_bc")
        binary_full_path = os.path.join(project_path, binary_name+".bc")
        runtime.run_klee(work_dir, driver, binary_full_path, test_list, crash_info, logger, fix_loc)

        # restore original source code
        sym_var_inserter.mv_original_file_back()

        # create result folder
        log_path = os.path.join(source_path, "result"+str(index))
        if not os.path.isdir(log_path):
            command = "mkdir " + log_path
            subprocess.call(command, shell=True)
        fix_stm = os.path.join(log_path, "fix_stm.txt")
        patch_path = os.path.join(log_path, "patch")
        constraint_path = os.path.join(log_path, "constraints.txt")

        # read fix line and save it in the fix_stmt file
        fix_line = utils.read_fix_line(project_path, fix_loc.get_refined_file_name(), fix_loc.line_no-1)
        with open(fix_stm, 'w+') as f:
            f.write(fix_line + "positive")
        logger.info("fix_line is " + fix_line)

        # save the CFC' (generated by backward propagating crash-free-constraint CFC) into file
        save_log(source_path, work_dir + "/constraints.txt", "result"+str(index))
        logger.info("backward propagated constraint is save in " + constraint_path)

        with open(constraint_path, 'r') as f:
            constraint = f.readline()[:-1]
        #    logger.debug("backward propagated constraint (CFC') is " + constraint)

        # failed to backward propagate constraints
        if constraint == 'false' or constraint == 'true':
            # directly use the crash-free-constraint as patch
            with open(patch_path, 'w') as f:
                # TODO: negate constraint and add return statement
                ret = utils.infer_return_value(project_path, crash_info.get_function_name(),
                                       crash_info.get_refined_name(), logger)
                patch = "if(!"+crash_info.get_cfc()+") return " + ret + ";"
                f.write(patch)
                logger.info("Found plausible patch " + patch)
                logger.info("generated patches are saved in " + log_path)
                utils.apply_path(logger, project_path, source_path, fix_loc.get_refined_file_name(),
                                 fix_loc.line_no-1, patch, patch_path, "insert")
        else:
            # invoke second-order synthesizer and save generated patch into file
            synthesizer = os.path.join(full_path, "synthesis", "second_order", "so_synthesizer.py")
            command = "python3 " + " " + synthesizer + " " + log_path + " " + constraint_path + " " + fix_stm
            subprocess.call(command, shell=True)
            logger.debug("synthesize command : " + command)
            with open(patch_path, 'r') as f:
                patch = f.readline()
                logger.debug("Found plausible patch: " + fix_line + " => " + patch)
            logger.info("generated patches are saved in " + log_path)

            utils.apply_path(logger, project_path, source_path, fix_loc.get_refined_file_name(),
                             fix_loc.line_no-1, patch, patch_path, "replace")
        sym_var_inserter.mv_original_file_back()

        index += 1
        break
    logger.info("execution time (in minutes) is: " + str(time.time()-start_time))


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
                        help='the binary name', required=True)

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

