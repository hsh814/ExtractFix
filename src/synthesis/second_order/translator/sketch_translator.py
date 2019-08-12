from pyparsing import *
from translator.operators import cpp2z3
from translator import operators
from util import common


"""
<bool-A> :: <bool-B> | <bool-B>||<bool-A>
<bool-B> :: <bool-C> | <bool-C>&&<bool-B>
<bool-C> :: <bool-D> | !<bool-C>
<bool-D> :: (<bool-A>) | true | false | <cmp> | <var>
<cmp> :: <int-A> < <int-A> | <int-A> <= <int-A> | <int-A> > <int-B> | <int-A> >= <int-B> | <int-A> == <int-B> | <int-A> != <int-B>
<int-A> :: <int-B> | <int-A> + <int-B> | <int-A> - <int-B>
<int-B> :: <int-C> | <int-B> * <int-C> | <int-B> / <int-C>
<int-C> :: (<int-A>) | <number> | <var>
"""

class ExprInfo:
    def __init__(self, expr, expr_type=None):
        self.is_special = False
        self.true_name = expr
        if type(expr) == str:
            expr = "".join(list(filter(lambda x: x.isalnum() or x == '_', expr)))
        if expr != self.true_name:
            self.is_special = True
            common.special_var_table[expr] = self.true_name
        self.type = expr_type
        self.expr = expr
        self.extra_left = ""

    def set_type(self, expr_type):
        if expr_type is None:
            return
        if self.type is None:
            self.type = expr_type
        elif self.type != expr_type:
            assert False

    def __str__(self):
        if self.is_special:
            return self.true_name
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
    if operator in "+-*/":
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

def _rename_left_variable(expr, variable_name):
    #print("rename ", expr)
    if not isinstance(expr, ExprInfo):
        return
    if type(expr.expr) == list:
        for subexpr in expr.expr:
            _rename_left_variable(subexpr, variable_name)
    if type(expr.expr) == str and expr.expr == variable_name:
        expr.expr = "prevalue__" + expr.expr

def _parse_assign(expr):
    #print(expr)
    assert len(expr) == 3 or len(expr) == 4
    operator = expr[1]
    if type(operator) == list and len(operator) == 2:
        first_operator = operator[0]
        left_expr = expr[0] if len(expr) == 3 else expr[1]
        right_expr = expr[-1]
        expr[-1] = _build_expr(first_operator, [ExprInfo(left_expr.expr, left_expr.type), right_expr])
    extra_left = ""
    if len(expr) == 4:
        if expr[0] == "int":
            expr[3].set_type("Int")
        elif expr[0] == "bool":
            expr[3].set_type("Bool")
        else:
            assert False
        extra_left = expr[0] + " "
        expr = expr[1:]
    expr[0].set_type(expr[2].type)
    _rename_left_variable(expr[2], expr[0].expr)
    res = ExprInfo(["=", expr[0], expr[2]], "Assign")
    res.extra_left = extra_left
    return res

def _parse_self_add(expr):
    print("self add", expr)
    assert len(expr) == 2
    if type(expr[1]) == ExprInfo:
        expr[0], expr[1] = expr[1], expr[0]
    right = None
    if expr[1] == "++":
        right = _parse_left_first([ExprInfo(1, "Int"), "+", expr[0]])
    else:
        right = _parse_left_first([expr[0], "-", ExprInfo(1, "Int")])
    print(right.type)
    return _parse_assign([ExprInfo(expr[0].expr, expr[0].type), "=", right])

def _pre_process(sketch_str):
    sketch = sketch_str.strip()
    # if (condition) then {
    if sketch[:2] == "if":
        left = sketch.index('(')
        count = 0
        right = -1
        for i in range(left, len(sketch)):
            if sketch[i] == '(':
                count += 1
            elif sketch[i] == ')':
                count -= 1
                if count == 0:
                    right = i
                    break
        assert right >= 0
        return sketch[:left+1], sketch[left+1: right], sketch[right:]
    elif sketch[:3] == "for":
        first = sketch.index(';')
        second = sketch.index(';', first + 1)
        if second == first + 1:
            return sketch[:first+1], "true", sketch[second:]
        else:
            return sketch[:first+1], sketch[first+1: second], sketch[second:]
    elif sketch[:5] == "while":
        left = sketch.index("(")
        count = 0
        right = -1
        for i in range(left, len(sketch)):
            if sketch[i] == "(":
                count += 1
            elif sketch[i] == ")":
                count -= 1
                if count == 0:
                    right = i
                    break
        assert right >= 0
        return sketch[:left+1], sketch[left+1: right], sketch[right:]
    if sketch[-1] == ';':
        return "", sketch[:-1], ';'
    return "", sketch, ""

def _trans_expr_info_to_cpp(exprInfo):
    expr = exprInfo.expr
    if type(expr) == list:
        operator = operators.z32cpp[expr[0]]
        arg = list(map(lambda x: _trans_expr_info_to_cpp(x), expr[1:]))
        if len(arg) == 1:
            return operator + "(" + arg[0] + ")"
        elif len(arg) == 2:
            return "(" + arg[0] + operator + arg[1] + ")"
        else:
            assert False
    elif type(expr) == str:
        return expr
    elif type(expr) == tuple:
        if expr[0] == "Int":
            return str(expr[1])
        elif expr[0] == "Bool":
            return "true" if expr[1] else "false"
        else:
            assert False
    elif exprInfo.type == "Int":
        assert type(expr) == int
        return str(expr)
    elif exprInfo.type == "Bool":
        assert type(expr) == bool
        return "true" if expr else "false"
    else:
        assert False

def _parse_var(expr):
    name = ""
    for sub_expr in expr:
        if type(sub_expr) == ExprInfo:
            name += _trans_expr_info_to_cpp(sub_expr)
        else:
            name += str(sub_expr)
    return ExprInfo(name)

def parse_sketch(sketch_str):
    left, sketch_str, right = _pre_process(sketch_str)
    hex = Regex(r'0x([0-9a-f]+)').setParseAction(lambda x: ExprInfo(int(x[0], 0), "Int"))
    decimal = Regex(r'(-?0|-?[0-9]\d*)|(NULL)').setParseAction(
        lambda x: ExprInfo(0, "Int") if x[0] == "NULL" else ExprInfo(int(x[0], 0), "Int"))
    var = Forward()
    op_pointer = Regex(r"->")
    comma = Regex(r",")
    LPAR, RPAR = "()"
    LSQR, RSQR = "[]"
    token = Regex(r'(?!(true|false|NULL))[_a-zA-Z][_a-zA-Z0-9]*')
    op_add = Regex(r"\+|-")
    op_mul = Regex(r"\*|/")
    op_cmp = Regex(r"(<=)|(<)|(>=)|(>)|(==)|(!=)")
    op_and = Regex(r"&&")
    op_or = Regex(r"\|\|")
    op_not = Regex(r"\!")
    op_self_add = Regex(r"(\+\+)|(--)")
    op_operator = (op_add ^ op_mul)
    op_assign = Group((op_operator + "=") ^ "=")
    int_type = Regex(r"int")
    bool_type = Regex(r"bool")
    boolean = Regex(r'true|false').setParseAction(lambda x: ExprInfo(True if x[0] == "true" else False, "Bool"))
    int_A = Forward()
    int_B = Forward()
    int_C = (LPAR + int_A + RPAR).setParseAction(lambda x: x[1]) ^ var ^ decimal ^ hex
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
    arith_expr = (bool_A ^ int_A)
    pointer_token = (token + ZeroOrMore(op_pointer + token))
    array_token = (pointer_token + ZeroOrMore(LSQR + arith_expr + RSQR)).setParseAction(_parse_var)
    var << (array_token ^ (pointer_token + LPAR + arith_expr + ZeroOrMore(comma + arith_expr) + RPAR)).setParseAction(_parse_var)
    assign = ((Optional(int_type) + var + op_assign + int_A).setParseAction(_parse_assign) ^
              (Optional(bool_type) + var + op_assign + bool_A).setParseAction(_parse_assign))
    self_add = ((op_self_add + var) ^ (var + op_self_add)).setParseAction(_parse_self_add)
    expr = bool_A ^ assign ^ self_add
    result = expr.parseString(sketch_str, parseAll=True)[0]
    #print(result)
    left += result.extra_left
    if result.type is None:
        result.set_type("Bool")
    #print(result)
    return left, result, right

if __name__ == "__main__":
    tests = ["a[b]",
             "a->b[34][198][c(d[123][456])]",
             "x(y->z,w+1,an)",
             "if ((tlen > 0) && (xmlStrncmp(ctxt->input->cur, ctxt->name, tlen) == 0)) {",
             "x->y->z",
             "i <= 10",
             "++x",
             "int x = 0x20",
             "while (((x > y) && (y < z)) || !w) {",
             "for (;;) {",
             "for (int i = 1; i <= 10 && y > z; i += 5)",
             "if (x > 10) then x = 1;",
             "int x = 1+3",
             "!!!!!x",
             "bool x = (y+z) != 0|| !!!(!(!!(!(w))))",
             "(((x)))",
             "x<=y",
             "!x==0",
             "(x+y)*asd <= (x+y) || !x==0 && !!z || w*x < 0",
             "result = x*y+z-w*10+k",
             "x=y"]
    for test in tests:
        left, result, right = parse_sketch(test)
        print(str(result.type) + ":", result, left, right)