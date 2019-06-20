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


class Sanitizer:
    def __init__(self, source_path, compile_command):
        self.source_path = source_path
        self.compile_command = compile_command

    def _default_generate_crash_info(self):
        pass


class BufferOverflowSanitizer(Sanitizer):
    def __init__(self, source_path, compile_command):
        Sanitizer.__init__(self, source_path, compile_command)

    def generate_crash_info(self):
        # TODO: call low fat
        # here, you need to compile the project by yourself
        crash_info = Global.CrashInfo("main", 51, {})
