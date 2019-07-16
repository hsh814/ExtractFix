import sys
import os
from instrumentation_utils import *
import logging
import commands
import argparse

# from GSInserter import getFiles, getImportHeadFolders
# TODO: may need to change in different system

callee_tmp_file = '/tmp/callee.txt'

source_dir = os.path.dirname(os.path.realpath(__file__))


def preprocess_single_file(mission, f, tail, logger):
    cmd = source_dir+'/GSInserter -mission=' + mission + " " + f + tail

    # logger.debug('Executing >>>>>>>>'+cmd)

    try:
        (status, output) = commands.getstatusoutput(cmd)
    except:
        e = sys.exc_info()[0]
        logger.fatal(e)

    return output


def preprocess(args, logger):
    project_base = args.base
    lib = args.lib
    globalize = args.globalize
    __preprocess(project_base, lib, globalize, logger)


def __preprocess(project_base, lib=False, globalize=False, logger=logging):
    # TODO: configure fisrt
    # configure the project to generate the full headers
    # check the configure file exists
    # assert os.path.isfile(project_base + "/configure")

    if os.path.exists(callee_tmp_file):
        os.remove(callee_tmp_file)

    files = get_files(project_base, '.c')
    include_options = get_import_head_folders(project_base, system_header)

    tail = ' -- ' + ' '.join(include_options)

    if lib:
        logger.debug('>>>>>>>> REPLACE UNSUPPORTED LIB >>>>>>>>')
        for c_file in files:
            output = preprocess_single_file('replace-flib', c_file, tail, logger)
            # logger.debug(output)
            assert 'core dump' not in output

    if globalize:
        logger.debug('>>>>>>>> INSERT GLOBAL MALLOC SIZE >>>>>>>>')
        for c_file in files:
            cotail = ' -callee-out=' + callee_tmp_file + tail
            output = preprocess_single_file('replace-size', c_file, cotail, logger)
            # logger.debug(output)
            assert 'core dump' not in output

        logger.debug('>>>>>>>> DECLARE GLOBAL MALLOC SIZE >>>>>>>>')
        for c_file in files:
            cotail = ' -callee-out=' + callee_tmp_file + tail
            output = preprocess_single_file('declare-size', c_file, cotail, logger)
            # logger.debug(output)
            assert 'core dump' not in output


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Target project preprocessor.')
    parser.add_argument("-b", "--base", help="set the base path of the project", required=True)
    parser.add_argument("-v", "--verbose", help="increase output verbosity", action="store_true", default=False)

    group = parser.add_argument_group('Set the mission type')
    group.add_argument("-g", "--globalize", help="globalize the malloc() argu", action="store_true", default=False)
    group.add_argument("-l", "--lib", help="replace the unsupported libraries", action="store_true", default=False)

    args = parser.parse_args()

    if (not args.globalize) and (not args.lib):
        parser.print_usage()
        sys.exit('The option -g and -l must be set at least one')

    logging.basicConfig()
    logger = logging.getLogger('Crash-free-fix Preprocess: ' + args.base)

    if args.verbose:
        logger.setLevel(logging.DEBUG)

    assert not os.path.isfile(args.base)

    preprocess(args, logger)

