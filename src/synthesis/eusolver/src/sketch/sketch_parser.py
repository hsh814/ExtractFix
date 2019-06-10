#!/usr/bin/env python3

def filter_sexp_for(head, file_sexp):
    curr = []
    rest = []
    for sexp in file_sexp:
        if sexp[0] == head:
            curr.append(sexp[1:])
        else:
            rest.append(sexp)
    return curr, rest

def flatten(sketch):
    retval = []
    for item in sketch:
        if type(item) is list:
            retval.append("(")
            retval += flatten(item)
            retval.append(")")
        elif type(item) is tuple:
            retval.append(str(item[1]))
        else:
            retval.append(item)
    return retval

def extract_sketch(file_expr):
    global sketch
    sketch, file_expr = filter_sexp_for("sketch", file_expr)
    assert file_expr==[]
    sketch = flatten(sketch[0])
    return sketch
