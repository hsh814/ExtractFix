from parser import sexp
from translator import operators, sketch_translator
from translator.sketch_translator import ExprInfo
from util import common
import config

def _translate_operator(constraint, translate_table):
    if type(constraint) == str:
        return constraint
    if type(constraint) == tuple:
        return constraint
    if type(constraint) == list:
        assert type(constraint[0]) == str
        operator = constraint[0]
        if operator in translate_table:
            operator = translate_table[operator]
        result = list(map(lambda subexpr: _translate_operator(subexpr, translate_table), constraint))
        result[0] = operator
        return result
    assert False

def _get_z3_operator_info(operator):
    if operator in ["+", "-", "*", "div"]:
        return [["Int", "Int"], "Int"]
    if operator in [">", ">=", "<", "<="]:
        return [["Int", "Int"], "Bool"]
    if operator == "=":
        return [[None, None], "Bool"]
    if operator in ["and", "or"]:
        return [["Bool", "Bool"], "Bool"]
    if operator == "not":
        return [["Bool"], "Bool"]
    assert False

def _assign_type(expr):
    #print(expr)
    if type(expr) == str:
        return ExprInfo(expr)
    if type(expr) == tuple:
        assert expr[0] in ["Int", "Bool"]
        return ExprInfo(expr[1], expr[0])
    if type(expr) == list:
        operator = expr[0]
        arg_type, return_type = _get_z3_operator_info(operator)
        assert len(expr) == len(arg_type) + 1
        arg_list = list(map(lambda x: _assign_type(x), expr[1:]))
        for (i, var_type) in enumerate(arg_type):
            arg_list[i].set_type(var_type)
        if operator == "=":
            if arg_list[0].type == "Int" and arg_list[1].type == "Bool":
                assert type(arg_list[0].expr) == int
                arg_list[0] = ExprInfo(arg_list[0].expr != 0, "Bool")
            if arg_list[1].type == "Int" and arg_list[0].type == "Bool":
                assert type(arg_list[1].expr) == int
                arg_list[1] = ExprInfo(arg_list[1].expr != 0, "Bool")
            arg_list[0].set_type(arg_list[1].type)
            arg_list[1].set_type(arg_list[0].type)
        result = [operator]
        result.extend(arg_list)
        return ExprInfo(result, return_type)

def _parse_constraint(constraint):
    #print(constraint)
    result = sexp.sexp.parseString(constraint, parseAll=True).asList()[0]
    result = _translate_operator(result, operators.klee2z3str)
    result = _assign_type(result)
    if result.type is None: result.set_type("Bool")
    return result

def _collect_used_component(expr_info, variable_table, constant_table, operator_list):
    expr = expr_info.expr
    print(expr, type(expr))
    expr_type = expr_info.type
    if type(expr) == list:
        if expr[0] not in operator_list: operator_list.append(expr[0])
        for sub_expr in expr[1:]:
            _collect_used_component(sub_expr, variable_table, constant_table, operator_list)
        return
    if type(expr) == str:
        #print(expr_info.expr, expr_info.type)
        if expr not in variable_table:
            variable_table[expr] = expr_info
        variable_table[expr].set_type(expr_type)
        return
    if type(expr) == int:
        assert expr_type == "Int"
        if abs(expr) > config.constant_limit:
            return
        for i in range(expr - config.constant_expend_size, expr + config.constant_expend_size + 1):
            if str(i) not in constant_table[expr_type]:
                constant_table[expr_type].append(str(i))
        return
    if type(expr) == bool:
        assert expr_type == "Bool"
        constant_table[expr_type] = ["true", "false"]
        return
    assert False

def _get_symbol(expr_type):
    if expr_type == "Int":
        return "Start"
    if expr_type == "Bool":
        return "StartBool"
    if expr_type == "Cons":
        return "Constant"
    assert False

def _make_declare(function_info, variable_table, constant_table, operator_list):
    arg_list = []
    for var_name, var_info in variable_table.items():
        arg_list.append([var_name, var_info.type])
    declare_result = ["synth-fun", function_info.expr, arg_list, function_info.type]
    rule_table = {"Start": ["Int"], "StartBool": ["Bool"]}
    for constant_type, value_list in constant_table.items():
        symbol = _get_symbol(constant_type)
        for value in value_list:
            rule_table[symbol].append(str(value))
    is_use_constant = False
    for operator in operator_list:
        operator_arg_list, return_type = _get_z3_operator_info(operator)
        symbol = _get_symbol(return_type)
        if operator == "=":
            rule_table["StartBool"].append(["=", "Start", "Start"])
            rule_table["StartBool"].append(["=", "StartBool", "StartBool"])
            continue
        elif operator == "div":
            rule_table["Start"].append(["div", "Start", "Constant"])
            is_use_constant = True
            continue
        operator_arg_list = list(map(lambda x: _get_symbol(x), operator_arg_list))
        result = [operator]
        result.extend(operator_arg_list)
        rule_table[symbol].append(result)
    if is_use_constant:
        rule_table["Constant"] = ["Int"]
        for constant_type, value_list in constant_table.items():
            if constant_type == "Int":
                for value in value_list:
                    if value != "0":
                        rule_table["Constant"].append(str(value))
    for name, var_type in arg_list:
        symbol =  _get_symbol(var_type)
        rule_table[symbol].append(name)
    rule_list = []
    for name, rule in rule_table.items():
        if len(rule) > 1:
            rule_list.append([name, rule[0], rule[1:]])
    declare_result.append(rule_list)
    return declare_result

def _list_to_str(expr):
    if type(expr) == list:
        return "(" + " ".join(list(map(lambda x: _list_to_str(x), expr))) + ")"
    return str(expr)

def _substitute_function_call(expr, function_name, function_call):
    if type(expr) == str and expr == function_name:
        return function_call
    if type(expr) == list:
        return list(map(lambda x: _substitute_function_call(x, function_name, function_call), expr))
    return expr

def trans(constraint_file, sketch_file):
    with open(constraint_file, "r") as f:
        all_inp = f.readlines()
        #import pprint as pp
        #pp.pprint(all_inp)
    is_negative = False
    with open(sketch_file) as f:
        sketch = f.readlines()
        assert len(sketch) == 1 or len(sketch) == 2
        if len(sketch) == 2 and "negative" in sketch[1]:
            #print("negative")
            is_negative = True
        sketch = sketch[0]
    all_inp = list(map(lambda x: x.strip(), all_inp))
    all_inp = list(filter(lambda x: len(x) > 0, all_inp))
    #TODO support multiline fix
    #print(all_inp[-1])
    left_sketch, sketch, right_sketch = sketch_translator.parse_sketch(sketch)
    constraint = _parse_constraint(" ".join(all_inp))
    #print(sketch, constraint)
    variable_table = {}
    constant_table = {"Int": [], "Bool": []}
    operator_list = ["<", "<=", "and", "or", "not"]
    constraint.simplify()
    sketch.simplify()
    print("constraint")
    _collect_used_component(constraint, variable_table, constant_table, operator_list)
    print("sketch")
    _collect_used_component(sketch, variable_table, constant_table, operator_list)
    for variable, variable_info in variable_table.items():
        assert variable_info.type is not None
    if sketch.type == "Assign":
        func = sketch.expr[1]
        sketch = sketch.expr[2]
        assert func.type is not None
        assert func.expr in variable_table
        left_sketch += func.expr + " = "
        del variable_table[func.expr]
    else:
        func = ExprInfo("condition", "Bool")
        if is_negative:
            constraint = ExprInfo(["=>", ExprInfo(["not", func], "Bool"), constraint], "Bool")
        else:
            constraint = ExprInfo(["=>", func, constraint], "Bool")
        #print(constraint)
        #print(constraint)
    syn_declare = [_make_declare(func, variable_table, constant_table, operator_list)]
    arg_list = syn_declare[0][2]
    #print(arg_list)
    func_call = [func.expr]
    func_call.extend(list(map(lambda x: x[0], arg_list)))
    var_declare = []
    for name, variable_info in variable_table.items():
        var_declare.append(["declare-var", variable_info.expr, variable_info.type])
    constraint_declare = [["constraint", constraint.as_list()]]
    constraint_declare = _substitute_function_call(constraint_declare, func.expr, func_call)
    sketch_declare = [["sketch", func.expr, sketch.as_list()]]
    sl_result = []
    sl_result.extend(syn_declare)
    sl_result.extend(var_declare)
    sl_result.extend(constraint_declare)
    sl_result.extend(sketch_declare)
    #import pprint as pp
    #pp.pprint(sl_result)
    with open("mid.sl", "w") as oup:
        oup.write("\n".join(list(map(lambda x: _list_to_str(x), sl_result))))
    return left_sketch, right_sketch

def trans_to_cpp(patch):
    if type(patch) == list:
        operator = operators.z32cpp[patch[0]]
        arg = list(map(lambda x: trans_to_cpp(x), patch[1:]))
        if len(arg) == 1:
            return "(" + operator + arg[0] + ")"
        elif len(arg) == 2:
            return "(" + arg[0] + operator +  arg[1] + ")"
        else:
            assert False
    elif type(patch) == str:
        if patch in common.special_var_table:
            return "(" + common.special_var_table[patch] + ")"
        return "(" + patch + ")"
    elif type(patch) == tuple:
        if patch[0] == "Int":
            return "(" + str(patch[1]) + ")"
        elif patch[0] == "Bool":
            return "true" if patch[1] else "false"
        else:
            assert False
    else:
        assert False