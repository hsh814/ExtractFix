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

import os, subprocess
from Global import *
import re


class FaultLocalization:
    def __init__(self, project_path, binary_name, func_list, crash_info, logger):
        self.project_path = project_path
        self.binary_name = binary_name
        self.func_list = func_list
        self.crash_info = crash_info
        self.logger = logger
        self.dir_path = os.path.dirname(os.path.realpath(__file__))

    def preprocess_func_list(self):
        stack = []
        stack.append(self.func_list[0])
        for i in range(1, len(self.func_list)):
            top = stack[-1]
            # find the crash function
            if top[1] == self.crash_info.function_name:
                break
            func = self.func_list[i]
            # find function pair in the stack
            if func[0] == 'OUT' and top[0] == 'IN' and func[1] == top[1]:
                stack.pop()
            else:
                stack.append(func)
        self.logger.debug("remaining function list after preprocess: " + str(stack))
        return stack

    def run_fix_loc_pass(self, func_list):
        binary_name = self.binary_name+".bc"
        lib_fix_loc = os.path.join(self.dir_path, "libLLVMFixLoc.so")

        # split the crash-free constraints as single variables
        crash_vars = re.sub(r'\W', " ", self.crash_info.cfc).split()
        crash_vars_list = []
        for item in crash_vars:
            if item not in crash_vars_list and not str(item).isdigit():
                crash_vars_list.append(item)

        crash_vars_list = " ".join(crash_vars_list)

        command = "opt -S -load=" + lib_fix_loc + " -fixloc " + binary_name + \
                  " -fun " + self.crash_info.function_name + \
                  " -no " + str(self.crash_info.line_no) + \
                  " -lf " + "\"" + func_list + "\"" + \
                  " -cv " + "\"" + crash_vars_list + "\"" + \
                  " > /dev/null"

        self.logger.debug("run FixLoc pass command: " + command)
        try:
            retval = subprocess.check_output(command, cwd=self.project_path, shell=True)
        except subprocess.CalledProcessError as e:
            self.logger.fatal("run FixLoc pass failed, command line: " + command)
            exit(1)

        self.logger.info("successfully run FixLoc pass")

        return retval

    def read_fix_loc_from_file(self):
        import json
        fix_locs = []
        with open('/tmp/fixlocations.json') as json_file:
            data = json.load(json_file)
            for p in data:
                message = p[0]
                file_name = p[1]
                function_name = p[2]
                line_no = p[3]
                sys_vars = p[4]
                fix_loc = FixLoc(message, file_name, function_name, line_no, sys_vars)

                fix_locs.append(fix_loc)
        return fix_locs

    def get_potential_fault_locs(self):
        func_list = " ".join(str(item[1]) for item in self.preprocess_func_list())
        fix_loc_log = self.run_fix_loc_pass(func_list)
        self.logger.debug("the results by running FixLoc: " + fix_loc_log)
        fix_locs = self.read_fix_loc_from_file()

        for fix_loc in fix_locs:
            self.logger.debug(fix_loc)
        return fix_locs

