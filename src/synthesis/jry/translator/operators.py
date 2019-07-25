klee2z3str = {
    "Not": "not",
    "Add": "+",
    "Sub": "-",
    "Mul": "*",
    #"Udiv":
    #"SDiv":
    #"URem":
    #"SRem":
    "And": "and",
    "Or": "or",
    "Xor": "xor",
    #"Shl":
    #"LShr":
    #"AShr":
    "Eq": "=",
    #"Ne":
    #"Ult":
    #"Ule":
    #"Ugt":
    #"Uge":
    "Slt": "<",
    "Sle": "<=",
    "Sgt": ">",
    "Sge": ">="
}

cpp2z3 = {
    "+": "+",
    "-": "-",
    "*": "*",
    "<": "<",
    "<=": "<=",
    ">": ">",
    ">=": ">=",
    "==": "=",
    "!": "not",
    "||": "or",
    "&&": "and",
    "=": "assign"
}

def get_z3_str(operator):
    if operator in klee2z3str:
        return klee2z3str[operator]
    assert False