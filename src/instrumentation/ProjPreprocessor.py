import sys
import os
import re
import logging
import commands

from GSInserter import getFiles, getImportHeadFolders

system_header = ['/usr/local/lib/clang/6.0.1/include']

callee_tmp_file = '/tmp/callee.txt'

def preprocess_single_file(mission, f, tail):
    cmd = './GSInserter -mission=' + mission + " " + f + tail

    # if 'tif_ovrcache.c' not in f:
    #     return ''

    print ('Executing >>>>>>>>\n%s\n') % (cmd)

    try:
        (status, output) = commands.getstatusoutput(cmd)
        print output
    except:
        e = sys.exc_info()[0]
        print e

    return output


def preprocess(project_base):

    # TODO: configure fisrt
    # configure the project to generate the full headers

    # check the configure file exists
    assert os.path.isfile(project_base + "/configure")

    if os.path.exists(callee_tmp_file):
        os.remove(callee_tmp_file)

    files = getFiles(project_base, '.c')
    include_options = getImportHeadFolders(project_base, system_header)

    tail = ' -- ' + ' '.join(include_options)

    logger.debug('>>>>>>>> REPLACE UNSUPPORTED LIB >>>>>>>>')
    for c_file in files:
        output = preprocess_single_file('replace-flib', c_file, tail)
        assert 'core dump' not in output

    logger.debug('>>>>>>>> INSERT GLOBAL MALLOC SIZE >>>>>>>>')
    for c_file in files:
        cotail = ' -callee-out=' + callee_tmp_file + tail
        output = preprocess_single_file('replace-size', c_file, cotail)
        assert 'core dump' not in output

    logger.debug('>>>>>>>> DECLARE GLOBAL MALLOC SIZE >>>>>>>>')
    for c_file in files:
        cotail = ' -callee-out=' + callee_tmp_file + tail
        output = preprocess_single_file('declare-size', c_file, cotail)
        assert 'core dump' not in output


if __name__ == "__main__":
    if len(sys.argv) == 2:
        project_base = sys.argv[1]
        # TODO mission type
    else:
        help = "Usage: ProjPreprocessor [PATH_TO_SOURCE] \n\n" \
               "-The project need to be configured firstly to generate some '.h' files\n\n"
        sys.exit(help)

    logging.basicConfig()
    logger = logging.getLogger('Crash-free-fix ')

    assert not os.path.isfile(project_base)

    preprocess(project_base)
