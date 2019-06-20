import sys
import os
import re


from pycparser import c_parser, c_ast, parse_file, c_generator

class FirstFuncDeclVisitor(c_ast.NodeVisitor):
    def __init__(self, file):
        self.fstFuncDeclLine = -1
        self.file = file
        self.current_parent = None

    def visit_FuncDecl(self, node):
        if self.fstFuncDeclLine == -1 and self.file == node.coord.file:

            #if self.current_parent is Decl:

            self.fstFuncDeclLine = node.type.type.coord.line

    def generic_visit(self, node):
        """ Called if no explicit visitor function exists for a
            node. Implements preorder visiting of the node.
        """
        oldparent = self.current_parent
        self.current_parent = node
        for c in node:
            self.visit(c)
        self.current_parent = oldparent

# A visitor with some state information (the funcname it's looking for)
class FuncCallVisitor(c_ast.NodeVisitor):
    def __init__(self, funcname):
        self.funcname = funcname
        self.mallocArgs = []
        self.generator = c_generator.CGenerator()
        self.current_parent = None

    def visit_FuncCall(self, node):
        if hasattr(node.name, 'name') and node.name.name == self.funcname:
            #print('%s called at %s' % (self.funcname, node.name.coord))

            for param in node.args:
                mallocLine = node.name.coord.line

                parentLine = self.current_parent.coord.line
                mallocSize = str(self.generator.visit(param))
                self.mallocArgs.append((parentLine, mallocLine, mallocSize))


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


def show_func_calls(fileName, funcname):
    ast = parse_file(fileName, use_cpp=True, cpp_args=['-E', r'-I'+dir_path+'/utils/fake_libc_include'])
    funcNameVisitor = FuncCallVisitor(funcname)
    funcNameVisitor.visit(ast)

    declVisitor = FirstFuncDeclVisitor(fileName)
    declVisitor.visit(ast)

    return funcNameVisitor.mallocArgs, declVisitor.fstFuncDeclLine


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

    newLine = pre + 'malloc(' + globalName + post
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


def process_single_file(filePath, blackList):
    func = 'malloc'

    with open(filePath, 'r') as file:
        if os.path.basename(file.name) in blackList:
            return

        data = file.read()

        if 'LOWFAT_GLOBAL' in data: # has already processed
            return

        result = re.search(r'\bmalloc\b', data)

        if result is None:
            return

    print('Processing: %s') % (filePath)

    insertList, headInsertLine = show_func_calls(filePath, func)

    if len(insertList) > 0:
        print('\tReplacing malloc')

    # for item in insertList:
    #     print(item)

    with open(filePath, 'r') as file:
        lines = file.readlines()
        insertList.reverse()

        headLines = []
        for index, item in enumerate(insertList):
            parentLine = int(item[0]) - 1  # get the parent line num
            mallocLine = int(item[1]) - 1  # get the malloc line num

            curLineStr = lines[mallocLine]

            assert 'malloc' in curLineStr

            globalName = 'LOWFAT_GLOBAL_MS_' + str(mallocLine)

            changed = change_malloc_line(curLineStr, globalName);
            lines[mallocLine] = changed

            mallocedSize = item[2]
            assign = '\n/*M_SIZE*/ ' + globalName + " = " + mallocedSize + ";\n"
            lines.insert(parentLine, assign)

            headLines.append("/*M_SIZE_G*/ size_t " + globalName + ";\n")


        for head in headLines:
            lines.insert(headInsertLine - 1, head)


        with open(filePath, 'w') as file:
           file.writelines(lines)
           file.flush()


def insert_gs(filename):
    files = []
    if os.path.isfile(filename):
        files.append(filename)
    else:
        files = get_files(filename, '.c')

        # sys.path.extend([filename + 'libtiff/', filename + 'port/',
        #                  '/home/nightwish/workspace/subjects/crash_free/libtiff_malloc/ori/libtiff/'])

    blakList = ['tif_win32.c', 'tif_vms.c', 'tif_wince.c', 'xtiff.c', 'tif2ras.c']

    for file in files:
        process_single_file(file, blakList)


if __name__ == "__main__":
    dir_path = os.path.dirname(os.path.realpath(__file__))
    if len(sys.argv) == 2:
        filename = sys.argv[1]
    else:
        sys.exit("usage: GSInserter [PATH_TO_SOURCR]")

    insert_gs(filename)

