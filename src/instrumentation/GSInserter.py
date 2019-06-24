import sys
import os
import re
import logging
from pycparser import c_parser, c_ast, parse_file, c_generator

# The folder holding this python script
dir_path = os.path.dirname(os.path.realpath(__file__))

class IdTypeVisitor(c_ast.NodeVisitor):
    def __init__(self):
        self.firstLine = sys.maxint

    def visit_IdentifierType(self, node):
        if node.coord is not None and node.coord.line < self.firstLine:
            self.firstLine = node.coord.line


class FirstFuncDeclVisitor(c_ast.NodeVisitor):
    def __init__(self, file):
        self.fstFuncDeclLine = -1
        self.file = file
        self.current_parent = None

    def visit_FuncDef(self, node):
        if self.fstFuncDeclLine == -1 and self.file == node.coord.file:
            # if self.current_parent is Decl:
            v = IdTypeVisitor()
            v.visit(node.decl)
            if v.firstLine != sys.maxint:
                self.fstFuncDeclLine = v.firstLine


    def generic_visit(self, node):
        """ Called if no explicit visitor function exists for a
            node. Implements preorder visiting of the node.
        """
        oldparent = self.current_parent
        self.current_parent = node
        for c in node:
            self.visit(c)
        self.current_parent = oldparent


class MallocCallee:
    def __init__(self, _file='', _calleeName='', _gv=''):
        self.file = _file
        self.calleeName = _calleeName
        self.gv = _gv

    def __str__(self):
        return self.calleeName + " @ " + self.file + " # " + self.gv


# A visitor with some state information (the funcname it's looking for)
class FuncCallVisitor(c_ast.NodeVisitor):

    def __init__(self, funcname):
        self.funcname = funcname
        self.mallocArgs = []
        self.generator = c_generator.CGenerator()
        self.mallocCallees = {}
        self.current_parent = None
        self.current_fname = ''

    def visit_FuncDef(self, node):
        if node.coord.file.endswith('.h'):
            return

        # TODO: complex
        if hasattr(node.decl, 'type'):
            if hasattr(node.decl.type, 'type'):
                if hasattr(node.decl.type.type, 'declname'):
                    self.current_fname = node.decl.type.type.declname
                elif hasattr(node.decl.type.type, 'type'):
                    self.current_fname = node.decl.type.type.type.declname

        for c in node:
            self.visit(c)

        self.current_fname = ''

    def visit_FuncCall(self, node):
        if hasattr(node.name, 'name') and node.name.name == self.funcname:
            #print('%s called at %s' % (self.funcname, node.name.coord))

            for param in node.args:
                mallocLine = node.name.coord.line

                parentLine = self.current_parent.coord.line
                mallocSize = str(self.generator.visit(param))

                # record the parameter
                self.mallocArgs.append((parentLine, mallocLine, mallocSize))

                assert self.current_fname != ''
                # record the callee, mallocLine -> callee
                self.mallocCallees[mallocLine] = self.current_fname

        # Visit args in case they contain more func calls.
        if node.args:
            self.visit(node.args)

    def generic_visit(self, node):
        """ Called if no explicit visitor function exists for a
            node. Implements preorder visiting of the node.
        """
        oldparent = self.current_parent
        self.current_parent = node
        for c in node:
            self.visit(c)
        self.current_parent = oldparent


def show_func_calls(fileName, funcname, include_dirs):
    cpp_args = ['-E', r'-I' + dir_path + '/utils/fake_libc_include']
    cpp_args.extend(include_dirs)

    ast = parse_file(fileName, use_cpp=True, cpp_args=cpp_args)
    funcNameVisitor = FuncCallVisitor(funcname)
    funcNameVisitor.visit(ast)

    declVisitor = FirstFuncDeclVisitor(fileName)
    declVisitor.visit(ast)

    return funcNameVisitor.mallocArgs, funcNameVisitor.mallocCallees, declVisitor.fstFuncDeclLine


def getFirstDeclLine(fileName, include_dirs):
    cpp_args = ['-E', r'-I' + dir_path + '/utils/fake_libc_include']
    cpp_args.extend(include_dirs)
    ast = parse_file(fileName, use_cpp=True, cpp_args=cpp_args)
    declVisitor = FirstFuncDeclVisitor(fileName)
    declVisitor.visit(ast)
    return declVisitor.fstFuncDeclLine


def change_malloc_line(line, globalName):

    idx = line.find('malloc')
    if idx < 0:
        return

    pre = line[0: idx]
    post = line[idx + len('malloc'): -1]

    stack = []
    stack.insert(0, post[post.find('(')])
    post = post[post.find('(') + 1 :]


    for idx in range(0, len(post)):
        ch = post[idx]
        if ch == '(':
            stack.insert(0, ch)
        elif ch == ')':
            stack.pop()
        if len(stack) == 0:
            break
    post = post[idx:]

    newLine = pre + 'malloc(' + globalName + post + '\n'
    return newLine

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


GENERATED_GVS =[]

def transfer_malloc_param(filePath, blackList, include_options, callees):
    func = 'malloc'

    # if filePath != "/home/nightwish/workspace/subjects/crash_free/libtiff_ig/libtiff/tif_unix.c":
    #   return
    # if filePath != '/home/nightwish/workspace/subjects/crash_free/libtiff_ig/contrib/dbs/tiff-grayscale.c':
    #    return

    with open(filePath, 'r') as f:
        if os.path.basename(f.name) in blackList:
            return

        data = f.read()

        # if has already processed
        if 'LOWFAT_GLOBAL' in data:
            return

        result = re.search(r'\bmalloc\b', data)

        if result is None:
            return

    # print('Processing: %s') % (filePath)

    insertList, calleeDict, headInsertLine = show_func_calls(filePath, func, include_options)

    # containts malloc invocation
    # if len(insertList) > 0:
    #     print('\tReplacing malloc')

    # for item in insertList:
    #    print(item)

    with open(filePath, 'r') as f:
        lines = f.readlines()
        insertList.reverse()

        headLines = []
        for index, item in enumerate(insertList):

            parentLineIdx = int(item[0]) - 1  # get the parent line num
            mallocLineIdx = int(item[1]) - 1  # get the malloc line num idx

            curLineStr = lines[mallocLineIdx]

            assert 'malloc' in curLineStr

            declFile = os.path.basename(f.name).split('.')[0]
            declFile = declFile.replace('-', '_')
            calleeFunc = calleeDict[item[1]]

            globalName = 'LOWFAT_GLOBAL_MS_' + declFile + '_' + calleeFunc + '_' + str(item[1])

            if globalName in GENERATED_GVS:
                print(globalName)
                assert False

            GENERATED_GVS.append(globalName)

            # skip if the callee function is main
            if calleeFunc != 'main':
                callee = MallocCallee(_file=filePath, _calleeName=calleeFunc, _gv=globalName)
                callees.append(callee)

            changed = change_malloc_line(curLineStr, globalName);
            lines[mallocLineIdx] = changed

            mallocedSize = item[2]
            assign = '\n/*M_SIZE*/ ' + globalName + " = " + mallocedSize + ";\n"
            lines.insert(parentLineIdx, assign)

            headLines.append("/*M_SIZE_G*/ size_t " + globalName + ";\n")

        for head in headLines:
            lines.insert(headInsertLine - 1, head)

        with open(filePath, 'w') as f:
            f.writelines(lines)
            f.flush()


def insert_global_size_decl(filePath, blackList, include_options, callees, logger):
    # if filePath != '/home/nightwish/workspace/subjects/crash_free/libtiff_ig/libtiff/tif_jpeg.c':
    #   return

    with open(filePath, 'r') as f:
        if os.path.basename(f.name) in blackList:
            return

        lines = f.readlines()
        data = '\n'.join(lines)

        headLines = []

        headInsertLine = getFirstDeclLine(filePath, include_options)
        if headInsertLine == -1:
            return

        for callee in callees:
            # it is no need to insert a same file
            if callee.file == filePath:
                continue

            # whether the file contains the callee function
            result = re.search(r'\b' + callee.calleeName + r'\b', data)
            if result is None:
                continue

            # logger.debug( '\tInserting global size: ' + callee.gv + ' @ ' + callee.calleeName + " in " + \
            #       os.path.basename(f.name) + " @ Line " + str(headInsertLine))

            headLines.append("/*M_SIZE_G*/ extern size_t " + callee.gv + ";\n")

        for head in headLines:
            lines.insert(headInsertLine - 1, head)

    with open(filePath, 'w') as f:
        f.writelines(lines)
        f.flush()


def getImportHeadFolders(project_base):
    headers = get_files(project_base, '.h')
    cpp_args = []
    for header in headers:
        opt = '-I' + header[0:header.rfind('/')]
        if opt not in cpp_args:
            cpp_args.append(opt)

    return cpp_args


def insert_gs(file_name, include_base, logger):
    files = []
    if os.path.isfile(file_name):
        files.append(file_name)
    else:
        files = get_files(file_name, '.c')

    include_options = getImportHeadFolders(include_base)

    # TODO: move to configure
    blackList = ['tif_win32.c', 'tif_vms.c', 'tif_wince.c',
                 'xtiff.c', 'tif2ras.c', 'tif_zip.c', 'tif_pixarlog.c', 'sgi2tiff.c',
                 'sgisv.c', 'tiffgt.c', 'tiffinfoce.c', 'tiff2dib.c', 'ras2tif.c',
                 'tif_pdsdirwrite.c', 'xtif_dir.c']

    logger.debug('>>>>>>>> TRANSFORMING MALLOC SIZE >>>>>>>>')
    callees = []
    for c_file in files:
        transfer_malloc_param(c_file, blackList, include_options, callees)

    logger.debug('>>>>>>>> INSERTING GLOBAL DECL >>>>>>>>')
    for c_file in files:
        insert_global_size_decl(c_file, blackList, include_options, callees, logger)


if __name__ == "__main__":
    if len(sys.argv) == 3:
        filename = sys.argv[1]
        include_base = sys.argv[2]
    else:
        help = "Usage: GSInserter [PATH_TO_SOURCE] [PATH_TO_INCLUDE_BASE]\n\n" \
               "-The project need to be configured firstly to generate some '.h' files\n\n"

        sys.exit(help)

    logging.basicConfig()
    logger = logging.getLogger('Crash-free-fix ')

    insert_gs(filename, include_base, logger)

