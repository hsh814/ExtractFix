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

from Global import *
import subprocess
from instrumentation_utils import *
import os


class SymVarInserter:
    def __init__(self, project_dir, logger, crash_info):
        self.logger = logger
        self.project_dir = project_dir
        self.crash_info = crash_info
        self.copied_files = {}
        self.file_index = 0
        self.cur_dir = os.path.dirname(os.path.abspath(__file__))

    def insert_sym_vars(self, fix_loc):

        crash_line_no = self.crash_info.get_line_no() - 2
        cfc = self.crash_info.get_cfc()
        crash_file = os.path.join(self.project_dir,
                                  self.crash_info.file_path,
                                  self.crash_info.file_name)
        self.save_original_file(crash_file)

        # TODO: insert symbolic variable at fix location, FixLoc is defined in Global
        file_name = fix_loc.get_file_name()
        file_name = file_name.replace("../", "")
        fix_file = os.path.join(self.project_dir,
                                file_name)
        self.save_original_file(fix_file)

        self.insert_cfc(crash_line_no, cfc, crash_file)

        fix_line_no = fix_loc.get_line_no()
        sys_vars = fix_loc.get_sym_vars()
        args = " ".join(sys_vars)

        inserter = os.path.join(self.cur_dir, "SVInserter")

        base_arg = ""
        if self.crash_info.get_base_name() != "":
            base_arg = " -base " + self.crash_info.get_base_name()

        include_options = get_import_head_folders(self.project_dir, system_header)
        tail = ' '.join(include_options)
        command = inserter + \
                  " -mission symbolize" + \
                  " -loc " + str(fix_line_no) + \
                  " -args \"" + args + "\"" + \
                  base_arg + \
                  " " + fix_file +\
                  " -- " + tail + \
                  " 2> /dev/null"

        self.logger.debug("insert symbolic variable command: " + command)
        try:
            subprocess.check_output(command, cwd=self.project_dir, shell=True)
        except subprocess.CalledProcessError as e:
            self.logger.fatal("error, command line: " + command)
            exit(1)
        self.insert_header(fix_file)
        self.insert_header(crash_file)

    def insert_cfc(self, crash_line_no, cfc, crash_file):
        include_options = get_import_head_folders(self.project_dir, system_header)

        inserter = os.path.join(self.cur_dir, "SVInserter")

        base_arg = ""
        if self.crash_info.get_base_name() != "":
            base_arg = " -base " + self.crash_info.get_base_name()

        tail = ' '.join(include_options)
        command = inserter + " -mission cfc" + \
                  " -loc " + str(crash_line_no) + \
                  " -args \"" + cfc + "\"" + \
                  base_arg + \
                  " " + crash_file + \
                  " -- " + tail + \
                  " 2> /dev/null"

        self.logger.debug("insert klee assume command: " + command)
        try:
            subprocess.check_output(command, cwd=self.project_dir, shell=True)
        except subprocess.CalledProcessError as e:
            self.logger.fatal("error, command line: " + command)
            exit(1)

    def insert_header(self, target_file):
        """ insert klee.h headers """
        with open(target_file, 'r+') as f:
            content = f.read()
            if "#include<klee/klee.h>" not in content:
                f.seek(0, 0)
                f.write("#include<klee/klee.h>\n" + content)

    def save_original_file(self, file_name):
        self.logger.debug("save original file " + file_name)
        target_dir = "/tmp/original_files/"
        if not os.path.isdir(target_dir):
            os.mkdir(target_dir)
        source_file = os.path.join(self.project_dir, file_name)
        target_file = os.path.join(target_dir, str(self.file_index))
        command = "cp " + source_file + " " + target_file
        subprocess.check_output(command, shell=True)
        self.copied_files[target_file] = source_file
        self.file_index += 1

    def mv_original_file_back(self):
        for target_file, source_file in self.copied_files.iteritems():
            command = "cp " + target_file + " " + source_file
            subprocess.check_output(command, shell=True)

        # command = "rm -rf /tmp/original_files/"
        # subprocess.check_output(command, shell=True)

