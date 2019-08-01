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

from enum import Enum


class BugType(Enum):
    """supported bug type"""
    buffer_overflow = 1
    integer_overflow = 2
    null_pointer = 3
    assertion_failure = 4
    api_specific = 5
    divide_by_0 = 6

    @staticmethod
    def list():
        return "[buffer_overflow, integer_overflow, null_pointer, assertion_failure, divide_by_0, api_specific]"


class CrashInfo:
    def __init__(self, file_path, file_name, function_name, line_no, cfc):
        self.file_path = file_path
        self.file_name = file_name
        self.function_name = function_name
        self.line_no = line_no
        self.cfc = cfc

    def get_file_name(self):
        return self.file_name

    def get_file_path(self):
        return self.file_path

    def get_function_name(self):
        return self.function_name

    def get_line_no(self):
        return self.line_no

    def get_cfc(self):
        return self.cfc

    def __str__(self):
        return str(self.__dict__)


class FixLoc:
    def __init__(self, message, file_name, function_name, line_no, sym_vars):
        self.message = message
        self.file_name = file_name
        self.function_name = function_name
        self.line_no = line_no
        self.sym_vars = sym_vars

    def get_message(self):
        return self.message

    def get_file_name(self):
        return self.file_name

    def get_refined_file_name(self):
        return self.file_name.replace("../", "")

    def get_function_name(self):
        return self.function_name

    def get_line_no(self):
        return self.line_no

    def get_sym_vars(self):
        return self.sym_vars

    def __str__(self):
        return str(self.__dict__)

