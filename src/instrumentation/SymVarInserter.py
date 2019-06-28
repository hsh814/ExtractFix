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
import subprocess, os


class SymVarInserter:
    def __init__(self, project_dir, logger, crash_info):
        self.logger = logger
        self.project_dir = project_dir
        self.crash_info = crash_info
        self.copied_files = {}
        self.file_index = 0

    def insert_sym_vars(self, fix_loc):
        # TODO: insert symbolic variable at fix location, FixLoc is defined in Global
        file_name = fix_loc.get_file_name()
        file_name = file_name.replace("../", "")
        self.save_original_file(file_name)

        self.insert_cfc()

    def insert_cfc(self):
        source_dir = os.path.join(self.project_dir,
                                  self.crash_info.file_path,
                                  self.crash_info.file_name)
        self.save_original_file(source_dir)

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
            command = "mv " + target_file + " " + source_file
            subprocess.check_output(command, shell=True)

        command = "rm -rf /tmp/original_files/"
        subprocess.check_output(command, shell=True)

