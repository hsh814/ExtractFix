import sys
import os
import re
import logging
import commands
import argparse

# from GSInserter import getFiles, getImportHeadFolders
# TODO: may need to change in different system
system_header = ['/usr/local/lib/clang/6.0.1/include']

callee_tmp_file = '/tmp/callee.txt'

source_dir = os.path.dirname(os.path.realpath(__file__))


def get_import_head_folders(project_base, system_header=[]):
    headers = get_files(project_base, '.h')
    cpp_args = []

    for folder in system_header:
        opt = '-I' + folder
        if opt not in cpp_args:
            cpp_args.append(opt)

    for header in headers:
        opt = '-I' + header[0:header.rfind('/')]
        if opt not in cpp_args:
            cpp_args.append(opt)

    return cpp_args


def get_files(target_dir, exetension):
    item_list = os.listdir(target_dir)

    file_list = list()
    for item in item_list:
        item_dir = os.path.join(target_dir, item)
        if os.path.isdir(item_dir):
            if item_dir.endswith('/test'):
                continue

            file_list += get_files(item_dir, exetension)
        else:
            if item_dir.endswith(exetension):
                file_list.append(item_dir)
    return file_list


def preprocess_single_file(mission, f, tail, logger):
    # if 'tif_ovrcache.c' not in f:
    #     return ''

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
    assert os.path.isfile(project_base + "/configure")

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

