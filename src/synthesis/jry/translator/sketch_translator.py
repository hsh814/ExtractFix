from pyparsing import *
from translator.operators import cpp2z3

"""
<bool-A> :: <bool-B> | <bool-B>||<bool-A>
<bool-B> :: <bool-C> | <bool-C>&&<bool-B>
<bool-C> :: <bool-D> | !<bool-C>
<bool-D> :: (<bool-A>) | true | false | <cmp> | <var>
<cmp> :: <int-A> < <int-A> | <int-A> <= <int-A> | <int-A> > <int-B> | <int-A> >= <int-B> | <int-A> == <int-B> | <int-A> != <int-B>
<int-A> :: <int-B> | <int-A> + <int-B> | <int-A> - <int-B>
<int-B> :: <int-C> | <int-B> * <int-C>
<int-C> :: (<int-A>) | <number> | <var>
"""

class ExprInfo:
    def __init__(self, expr, expr_type=None):
        self.type = expr_type
        self.expr = expr

    def set_type(self, expr_type):
        if expr_type is None:
            return
        if self.type is None:
            self.type = expr_type
        elif self.type != expr_type:
            assert False

    def __str__(self):
        if type(self.expr) == list:
            return "(" + " ".join(list(map(str, self.expr))) + ")"
        else:
            return str(self.expr)

    def as_list(self):
        if type(self.expr) != list:
            return self.expr
        result = [self.expr[0]]
        subexpr = list(map(lambda x: x.as_list(), self.expr[1:]))
        result.extend(subexpr)
        return result

    def simplify(self):
        if type(self.expr) != list:
            return
        for sub_expr in self.expr[1:]:
            sub_expr.simplify()
        if self.expr[0] == ">":
            self.expr = ["<", self.expr[2], self.expr[1]]
        elif self.expr[0] == ">=":
            self.expr = ["<=", self.expr[2], self.expr[1]]

def _get_operator_info(operator):
    if operator in "+-*":
        return [["Int", "Int"], "Int"]
    elif operator in [">", "<", ">=", "<=", "==", "!="]:
        return [["Int", "Int"], "Bool"]
    elif operator in ["||", "&&"]:
        return [["Bool", "Bool"], "Bool"]
    elif operator == "!":
        return [["Bool"], "Bool"]
    else:
        assert False

def _build_expr(operator, arg_list):
    operator_info = _get_operator_info(operator)
    assert len(operator_info[0]) == len(arg_list)
    for (i, arg) in enumerate(arg_list):
        arg.set_type(operator_info[0][i])
    result = [operator]
    result.extend(arg_list)
    if operator not in cpp2z3:
        assert operator == "!="
        result[0] = cpp2z3["=="]
        return _build_expr("!", [ExprInfo(result, "Bool")])
    else:
        result[0] = cpp2z3[result[0]]
        return ExprInfo(result, operator_info[1])

def _parse_left_first(expr):
    assert len(expr) % 2 == 1
    if len(expr) == 1:
        assert type(expr[0]) == ExprInfo
        return expr
    result = _build_expr(expr[1], [expr[0], expr[2]])
    for i in range(3, len(expr), 2):
        result = _build_expr(expr[i], [result, expr[i + 1]])
    return result

def _parse_assign(expr):
    assert len(expr) == 3 or len(expr) == 4
    if len(expr) == 4:
        if expr[0] == "int":
            expr[3].set_type("Int")
        elif expr[0] == "bool":
            expr[3].set_type("Bool")
        else:
            assert False
        expr = expr[1:]
    expr[0].set_type(expr[2].type)
    return ExprInfo(["=", expr[0], expr[2]], "Assign")

def parse_sketch(sketch_str):
    decimal = Regex(r'-?0|-?[0-9]\d*').setParseAction(lambda x: ExprInfo(int(x[0]), "Int"))
    var = Regex(r'(?!(true|false))[_a-zA-Z][_a-zA-Z0-9]*').setParseAction(lambda x: ExprInfo(x[0]))
    LPAR, RPAR = "()"
    op_add = Regex(r"\+|-")
    op_mul = Regex(r"\*")
    op_cmp = Regex(r"(<=)|(<)|(>=)|(>)|(==)|(!=)")
    op_and = Regex(r"&&")
    op_or = Regex(r"\|\|")
    op_not = Regex(r"\!")
    op_assign = Regex(r"=")
    int_type = Regex(r"int")
    bool_type = Regex(r"bool")
    boolean = Regex(r'true|false').setParseAction(lambda x: ExprInfo(True if x[0] == "true" else False, "Bool"))
    int_A = Forward()
    int_B = Forward()
    int_C = (LPAR + int_A + RPAR).setParseAction(lambda x: x[1]) ^ var ^ decimal
    int_B << (int_C + ZeroOrMore(op_mul + int_C)).setParseAction(_parse_left_first)
    int_A << (int_B + ZeroOrMore(op_add + int_B)).setParseAction(_parse_left_first)
    bool_A = Forward()
    bool_B = Forward()
    bool_C = Forward()
    bool_C << ((int_A + op_cmp + int_A).setParseAction(_parse_left_first) ^
               (LPAR + bool_A + RPAR).setParseAction(lambda x: x[1]) ^ boolean ^ var ^
               (op_not + bool_C).setParseAction(lambda x: _build_expr(x[0], [x[1]])))
    bool_B << (bool_C + ZeroOrMore(op_and + bool_C)).setParseAction(_parse_left_first)
    bool_A << (bool_B + ZeroOrMore(op_or + bool_B)).setParseAction(_parse_left_first)
    assign = ((Optional(int_type) + var + op_assign + int_A).setParseAction(_parse_assign) ^
              (Optional(bool_type) + var + op_assign + bool_A).setParseAction(_parse_assign))
    expr = bool_A ^ assign
    result = expr.parseString(sketch_str, parseAll=True)[0]
    if result.type is None:
        result.set_type("Bool")
    return result

if __name__ == "__main__":
    tests = ["int x = 1+3",
             "!!!!!x",
             "bool x = (y+z) != 0|| !!!(!(!!(!(w))))",
             "(((x)))",
             "x<=y",
             "!x==0",
             "(x+y)*asd <= (x+y) || !x==0 && !!z || w*x < 0",
             "result = x*y+z-w*10+k",
             "x=y"]
    for test in tests:
        result = parse_sketch(test)
        print(str(result.type) + ":", result)