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


class SymVarInserter:
    def __init__(self, project_dir, logger, crash_info):
        self.logger = logger
        self.project_dir = project_dir
        self.crash_info = crash_info

    def insert_sym_vars(self, fix_loc):
        # TODO: insert symbolic variable at fix location, FicLoc is defined in Global
        # TODO: I suggest coping the to-be-changed files into temporary directory and
        #  copy them back before trying the next fix location
        self.insert_cfc()

    def insert_cfc(self):
        # TODO: insert cfc at crash location, crash_info is defined in Global
        pass
