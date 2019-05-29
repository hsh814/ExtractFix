/* #########################################################################
This file is part of Fix2Fit.
Copyright (C) 2016

This is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
###########################################################################*/

#include <string>

#ifndef CRASH_FREE_FIX_GLOBAL_H
#define CRASH_FREE_FIX_GLOBAL_H

using std::string;

struct Config {
    bool verbose;
    string binaryPath;
    string binaryName;
};

extern struct Config config;

extern int ERROR_EXIT_CODE;
#endif //CRASH_FREE_FIX_GLOBAL_H
