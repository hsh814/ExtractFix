#########################################################################
# This file is part of crash-free-fix.
# Copyright (C) 2016

# This is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
###########################################################################

add_library( LLVMFuncTracer MODULE
        FuncTracer.cpp
        )

target_compile_features(LLVMFuncTracer PRIVATE cxx_range_for cxx_auto_type)

# LLVM is (typically) built with no C++ RTTI. We need to match that;
# otherwise, we'll get linker errors about missing RTTI data.
set_target_properties(LLVMFuncTracer PROPERTIES
        COMPILE_FLAGS "-fno-rtti"
        )

configure_file(GSInserter.py GSInserter.py COPYONLY)
configure_file(FuncTracer.py FuncTracer.py COPYONLY)
configure_file(__init__.py __init__.py COPYONLY)

