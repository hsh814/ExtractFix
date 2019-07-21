from parser import sexp
from translator import operators

def get_sl(path_condition, sketch_list):
    path_condition = sexp.sexp.parseString(path_condition, parseAll=True).asList()[0]
    sketch_list = sexp.sexp.parseString(sketch_list, parseAll=True).asList()[0]
