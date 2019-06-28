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

import os, sys
import subprocess


class FuncTracer:
    def __init__(self):
        self.dir_path = os.path.dirname(os.path.realpath(__file__))

    def insert_function_trace(self, project_path, logger, binary_name):
        binary_full_path = os.path.join(project_path, binary_name)
        lib_func_tracer = os.path.join(self.dir_path, "libLLVMFuncTracer.so")

        command = "opt -S -load=" + lib_func_tracer + " -func_tracer " + binary_full_path+".bc" + \
                  " > " + binary_full_path+"_with_func_tracer.ll"

        command2 = "llvm-as " + binary_full_path+"_with_func_tracer.ll" + \
                   " -o " + binary_full_path+"_with_func_tracer.bc"
        logger.debug("instrument with functracer command: " + command)
        try:
            subprocess.check_output(command, cwd=project_path, shell=True)
            subprocess.check_output(command2, cwd=project_path, shell=True)
        except subprocess.CalledProcessError as e:
            logger.fatal("run functracer failed, command line: " + command)

        logger.info("successfully instrument with functracer")

        return binary_full_path+"_with_func_tracer"

