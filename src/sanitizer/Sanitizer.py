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

import Global
import runtime
import os


class Sanitizer:
    def __init__(self, work_dir, logger):
        self.work_dir = work_dir
        self.logger = logger

    def _default_generate_crash_info(self):
        pass


class BufferOverflowSanitizer(Sanitizer):
    def __init__(self, work_dir, project_path, binary_name, driver, test_list, logger):
        Sanitizer.__init__(self, work_dir, logger)
        self.project_path = project_path
        self.binary_name = binary_name
        self.driver = driver
        self.test_list = test_list

    def generate_crash_info(self):
        runtime.project_config(self.work_dir, self.logger, "lowfat")
        runtime.project_build(self.work_dir, self.logger, "lowfat")

        binary_full_path = os.path.join(self.project_path, self.binary_name)
        runtime.run(self.work_dir, self.driver, binary_full_path, self.test_list, self.logger)

        self.logger.info("successfully run lowfat to generate crash-free constraints")

        crash_info = self.parse_crash_info()
        self.logger.debug("crash information is " + str(crash_info))
        return crash_info

    def parse_crash_info(self):
        if not os.path.isfile("/tmp/cfc.out"):
            self.logger.fatal("failed to generate crash free constraints")
            exit(2)
        f= open("/tmp/cfc.out", "r")
        line = f.readline()
        loc_cfc = line.split("#")
        assert (len(loc_cfc) == 2)

        location = loc_cfc[0]
        path_func_lineno = location.split(":")
        assert len(path_func_lineno) == 3
        line_no = int(path_func_lineno[2])
        function_name = path_func_lineno[1]

        file_path = path_func_lineno[0].replace("../", "")
        index = file_path.rfind("/")
        if index < 0:
            path = "."
            file_name = file_path
        else:
            path = file_path[0:index]
            file_name = file_path[index+1:]

        cfc = loc_cfc[1]
        start = cfc.find("(")
        end = cfc.rfind(")")
        assert (start < end)
        cfc = cfc[start+1:end]

        crash_info = Global.CrashInfo(path, file_name, function_name, line_no, cfc)
        return crash_info

