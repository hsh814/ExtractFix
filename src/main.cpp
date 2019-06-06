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

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#include <boost/filesystem.hpp>
#include <boost/program_options.hpp>

#include <boost/log/trivial.hpp>
#include <boost/log/core.hpp>
#include <boost/log/trivial.hpp>
#include <boost/log/expressions.hpp>
#include <boost/log/utility/setup/console.hpp>
#include <boost/log/utility/setup/common_attributes.hpp>

#include "fault_localization/FixLocation.h"
#include "synthesis/Synthesizer.h"
#include "util/DataStruct.h"
#include "util/WeakestPrecondition.h"
#include "Global.h"
#include "Runtime.h"

namespace po = boost::program_options;
namespace fs = boost::filesystem;

using std::string;
using std::vector;

int repair(string binaryFullPath, vector<string> tests){
    Runtime rt(binaryFullPath, tests);
    FixLocation fl(binaryFullPath, tests, rt);
    WeakestPrecondition wp(binaryFullPath);

    Location crashLoc = rt.getCrashLocation();
    /* generate crash free constraint at the crash location */
    Condition cfc = rt.generateCFC();

    vector<Location> fixLocations = fl.generateFixLocation();
    for (Location fixLoc: fixLocations){
        vector<Condition> wpc = wp.generateWPC(fixLoc, crashLoc, cfc);
    }
}

int main (int argc, char *argv[])
{
    po::options_description parser("Usage: crash-free-fix OPTIONS\n\nSupported options");
    parser.add_options()
            ("binary-path,p", po::value<string>()->value_name("Path"), "the path of the project binary")
            ("binary-name,n", po::value<string>()->value_name("Name"), "the name of the project binary")
            ("tests,t", po::value<vector<string> >()->multitoken()->value_name("Tests"), "the test input")
            ("verbose,v", "produce extended output")
            ("help,h", "produce help message and exit")
            ;
    po::variables_map vm;

    try {
        po::store(po::command_line_parser(argc, argv).options(parser).run(), vm);
        po::notify(vm);
    } catch(po::error& e) {
        BOOST_LOG_TRIVIAL(error) << e.what() << " (use --help)";
        return ERROR_EXIT_CODE;
    }

    if (vm.count("help")) {
        std::cout << parser << std::endl;
        return ERROR_EXIT_CODE;
    }

    if (vm.count("verbose")){
        config.verbose = true;
    }

    if (vm.count("binary-path")) {
        config.binaryPath = fs::absolute(vm["binary-path"].as<string>()).string();
    }

    if (!vm.count("binary-name")) {
        BOOST_LOG_TRIVIAL(error) << "binary is not specified (use --help)";
        return ERROR_EXIT_CODE;
    }
    config.binaryName = vm["binary-name"].as<string>();

    vector<string> tests;
    if (!vm.count("tests")) {
        BOOST_LOG_TRIVIAL(error) << "tests are not specified (use --help)";
        return ERROR_EXIT_CODE;
    }
    tests = vm["tests"].as<vector<string> >();


    std::stringstream binaryFullPath;
    binaryFullPath << config.binaryPath << "/" << config.binaryName;

    int ret = repair(binaryFullPath.str(), tests);
    if (ret != 0){
        BOOST_LOG_TRIVIAL(error) << "failed to generate patches";
        return ret;
    }
    return 0;
}