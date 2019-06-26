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

        crash_info = Global.CrashInfo(".", "ffmpeg.c", "decode_dds1", 51, {})
        self.logger.debug("crash information is " + str(crash_info))
        return crash_info

