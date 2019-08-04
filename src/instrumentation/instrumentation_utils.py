import os

system_header = os.environ['C_INCLUDE_PATH'].split(":")
system_header.append('/usr/local/lib/clang/6.0.1/include')


def get_import_head_folders(project_base, system_header=[]):
    headers = get_files(project_base, '.h')
    cpp_args = []

    for folder in system_header:
        opt = '-I' + folder
        if opt not in cpp_args:
            cpp_args.append(opt)

    for header in headers:
        if '/include/' in header:
            opt = '-I' + header[0 : header.rfind('/include/') + len('/include/')]
        else:
            opt = '-I' + header[0:header.rfind('/')]

        remain = True
        if "/tmp/proj_work_dir_coreutils" in project_base:
            if opt.endswith('/lib/sys') or opt.endswith('/lib/sys/'):
                remain = False

        if "/tmp/proj_work_dir_binutils" in project_base:
            if opt.endswith('/import/sys'):
                remain = False
            if opt.endswith('/build-gnulib/import'):
                remain = False
            if '/build-gnulib-gdbserver' in opt:
                remain = False

        if remain and opt not in cpp_args:
            cpp_args.append(opt)

    project_specific_header = os.path.join(project_base, "..", "project_specific_lib")
    opt = '-I' + project_specific_header
    cpp_args.append(opt)

    return cpp_args


def get_files(target_dir, extension):
    item_list = os.listdir(target_dir)

    file_list = list()
    for item in item_list:
        item_dir = os.path.join(target_dir, item)
        if os.path.isdir(item_dir):
            if item_dir.endswith('/test'):
                continue

            file_list += get_files(item_dir, extension)
        else:
            if item_dir.endswith(extension):
                file_list.append(item_dir)
    return file_list

