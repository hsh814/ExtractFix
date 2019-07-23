from parser import sexp
from translator import operators

def get_sl(bm, sketch_string):
    bm = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
    for

