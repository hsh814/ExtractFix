from pyparsing import *

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
        if self.type is None:
            self.type = expr_type
        elif self.type != expr_type:
            assert False

    def __str__(self):
        if type(self.expr) == list:
            return "(" + " ".join(list(map(str, self.expr))) + ")"
        else:
            return str(self.expr)

def _get_operator_info(operator):
    if operator in "+-*":
        return [["Int", "Int"], "Int"]
    elif operator in [">", "<", ">=", "<=", "==", "!="]:
        return [["Int", "Int"], "Bool"]
    elif operator in ["||", "&&"]:
        return [["Bool", "Bool"], "Bool"]
    else:
        assert False

def _build_expr(operator, arg_list):
    operator_info = _get_operator_info(operator)
    assert len(operator_info[0]) == len(arg_list)
    for (i, arg) in enumerate(arg_list):
        arg.set_type(operator_info[0][i])
    result = [operator]
    result.extend(arg_list)
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


def parse_sketch(sketch_str):
    decimal = Regex(r'-?0|-?[0-9]\d*').setParseAction(lambda x: ExprInfo(int(x[0]), "Int"))
    var_boolean = Regex(r'(?!(true|false))[_a-zA-Z][_a-zA-Z0-9]*').setParseAction(lambda x: ExprInfo(x[0], "Bool"))
    var_int = Regex(r'(?!(true|false))[_a-zA-Z][_a-zA-Z0-9]*').setParseAction(lambda x: ExprInfo(x[0], "Int"))
    LPAR, RPAR = "()"
    op_add = Regex(r"\+|-")
    op_mul = Regex(r"\*")
    op_cmp = Regex(r"<|>|<=|>=|\!=|==")
    op_and = Regex(r"&&")
    op_or = Regex(r"\|\|")
    boolean = Regex(r'true|false').setParseAction(lambda x: ExprInfo(True if x[0] == "true" else False, "Bool"))
    int_A = Forward()
    int_B = Forward()
    int_C = (LPAR + int_A + RPAR).setParseAction(lambda x: x[1]) ^ var_int ^ decimal
    int_B << (int_C + ZeroOrMore(op_mul + int_C)).setParseAction(_parse_left_first)
    int_A << (int_B + ZeroOrMore(op_add + int_B)).setParseAction(_parse_left_first)
    bool_A = Forward()
    bool_B = Forward()
    bool_C = (int_A + op_cmp + int_A).setParseAction(_parse_left_first) ^ \
             (LPAR + bool_A + RPAR).setParseAction(lambda x: x[1]) ^ boolean ^ var_boolean
    bool_B << (bool_C + ZeroOrMore(op_and + bool_C)).setParseAction(_parse_left_first)
    bool_A << (bool_B + ZeroOrMore(op_or + bool_B)).setParseAction(_parse_left_first)
    expr = int_A ^ bool_A
    return expr.parseString(sketch_str, parseAll=True)[0]

if __name__ == "__main__":
    tests = ["(x-y)*(x+y) < z || (y+x)>z && y != z"]
    for test in tests:
        print(parse_sketch(test))