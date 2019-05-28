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

#include <iostream>
#include "FixLocation.h"


FixLocation::FixLocation(string& binaryFullPath, vector<string>& tests)
                        :binaryFullPath(binaryFullPath), tests(tests){
    std::cout << "this is the constructor of FixLocation\n";
}

vector<Location> FixLocation::generateFixLocation(){
    std::cout << "this is the method to generate Fix Locations\n";
    vector<Location> fixLocs;
    return fixLocs;
}
