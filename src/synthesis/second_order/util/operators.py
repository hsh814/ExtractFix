import z3

string2python = {
    "+": lambda x: x[0] + x[1],
    "-": lambda x: x[0] - x[1],
    "*": lambda x: x[0] * x[1],
    "and": lambda x: x[0] and x[1],
    "or": lambda x: x[0] or x[1],
    "ite": lambda x: x[1] if x[0] else x[2],
    "not": lambda x: not x[0],
    "<": lambda x: x[0] < x[1],
    "<=": lambda x: x[0] <= x[1],
    ">": lambda x: x[0] > x[1],
    ">=": lambda x: x[0] >= x[1],
    "=>": lambda x: x[1] or (not x[0]),
    "=": lambda x: x[0] == x[1],
    "div": lambda x: x[0] // x[1]
}

string2z3 = {
    "+": lambda x: x[0] + x[1],
    "-": lambda x: x[0] - x[1],
    "*": lambda x: x[0] * x[1],
    "and": lambda x: z3.And(x),
    "or": lambda x: z3.Or(x),
    "ite": lambda x: z3.If(x[0], x[1], x[2]),
    "not": lambda x: z3.Not(x[0]),
    "<": lambda x: x[0] < x[1],
    "<=": lambda x: x[0] <= x[1],
    ">": lambda x: x[0] > x[1],
    ">=": lambda x: x[0] >= x[1],
    "=>": lambda x: z3.Implies(x[0], x[1]),
    "=": lambda x: x[0] == x[1],
    "div": lambda x: x[0] / x[1]
}

def use_signed_operator():
    MIN_INT = -2 ** 31
    MAX_INT = 2 ** 31 - 1
    INT_SIZE = 2 ** 32
    string2python["+"] = lambda x: x[0] + x[1] + INT_SIZE if x[0] + x[1] < MIN_INT \
        else x[0] + x[1] - INT_SIZE if x[0] + x[1] > MAX_INT \
        else x[0] + x[1]
    string2python["-"] = lambda x: x[0] - x[1] + INT_SIZE if x[0] - x[1] < MIN_INT \
        else x[0] - x[1] - INT_SIZE if x[0] - x[1] > MAX_INT \
        else x[0] - x[1]
    string2z3["+"] = lambda x: z3.If(x[0] + x[1] < MIN_INT, x[0] + x[1] + INT_SIZE,
                                     z3.If(x[0] + x[1] > MAX_INT, x[0] + x[1] - INT_SIZE, x[0] + x[1]))
    string2z3["-"] = lambda x: z3.If(x[0] - x[1] < MIN_INT, x[0] - x[1] + INT_SIZE,
                                     z3.If(x[0] - x[1] > MAX_INT, x[0] - x[1] - INT_SIZE, x[0] - x[1]))