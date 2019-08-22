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
        if operator[0] == "p":
            arg_list = list(map(lambda x: _assign_type(x), expr[1:]))
            result = [operator]
            result.extend(arg_list)
            return ExprInfo(result, None)
        #print(operator)
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

def _collect_used_component(expr_info, variable_table, constant_table, operator_list, private_variblae_table=None):
    expr = expr_info.expr
    #print(expr, type(expr))
    expr_type = expr_info.type
    if type(expr) == list:
        if expr[0] not in operator_list and expr[0][0] != "p":
            operator_list.append(expr[0])
        for sub_expr in expr[1:]:
            _collect_used_component(sub_expr, variable_table, constant_table, operator_list, private_variblae_table)
        return
    if type(expr) == str:
        #print(expr_info.expr, expr_info.type)
        if expr not in variable_table:
            variable_table[expr] = expr_info
        if private_variblae_table is not None:
            private_variblae_table[expr] = True
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

def trans_normal_klee(constraint_file, sketch_file):
    with open(constraint_file, "r") as f:
        all_inp = f.readlines()
    with open(sketch_file) as f:
        sketch_lines = f.readlines()
        assert len(sketch_lines) % 2 == 0
    all_inp = list(map(lambda x: x.strip(), all_inp))
    all_inp = list(filter(lambda x: len(x) > 0, all_inp))
    sketches = []
    for i in range(0, len(sketch_lines), 2):
        left_sketch, sketch, right_sketch = sketch_translator.parse_sketch(sketch_lines[i])
        sketches.append({"left_sketch": left_sketch,
                         "sketch": sketch,
                         "right_sketch": right_sketch,
                         "is_negative": "negative" in sketch_lines[i + 1]})
    constraint = _parse_constraint(" ".join(all_inp))
    #print(sketch, constraint)
    variable_table = {}
    private_variable_table = {}
    constant_table = {"Int": [], "Bool": []}
    operator_list = ["<", "<=", "and", "or", "not"]
    constraint.simplify()
    for sketch in sketches:
        sketch["sketch"].simplify()

    #print("constraint")
    _collect_used_component(constraint, variable_table, constant_table, operator_list)
    #print("sketch")
    for sketch in sketches:
        sketch["private_variable"] = {}
        _collect_used_component(sketch["sketch"], variable_table, constant_table, operator_list, sketch["private_variable"])
        for private_name in sketch["private_variable"]:
            private_variable_table[private_name] = True

    for variable, variable_info in variable_table.items():
        assert variable_info.type is not None

    pre_condition = None
    condition_count = 0
    for sketch in sketches:
        if sketch["sketch"].type == "Assign":
            sketch["func"] = sketch["sketch"].expr[1]
            sketch["sketch"] = sketch["sketch"].expr[2]
            assert sketch["func"].type is not None
            assert sketch["func"].expr in variable_table
            sketch["left_sketch"] += sketch["func"].expr + " = "
            del variable_table[sketch["func"].expr]
        else:
            condition_count += 1
            sketch["func"] = ExprInfo("condition" + str(condition_count), "Bool")
            if sketch["is_negative"]:
                current_condition = ExprInfo(["not", sketch["func"]], "Bool")
            else:
                current_condition = sketch["func"]
            if pre_condition is None:
                pre_condition = current_condition
            else:
                pre_condition = ExprInfo(["and", pre_condition, current_condition], "Bool")

    if pre_condition is not None:
        constraint = ExprInfo(["=>", pre_condition, constraint])
    syn_declare = []
    for sketch in sketches:
        sub_variable_table = {}
        for name, var in variable_table.items():
            if name not in sketch["private_variable"] and name in private_variable_table:
                continue
            sub_variable_table[name] = var
        current_function_declare = _make_declare(sketch["func"], sub_variable_table, constant_table, operator_list)
        syn_declare.append(current_function_declare)
        arg_list = current_function_declare[2]
        sketch["func_call"] = [sketch["func"]]
        sketch["func_call"].extend(list(map(lambda x: x[0], arg_list)))
    var_declare = []
    for name, variable_info in variable_table.items():
        var_declare.append(["declare-var", variable_info.expr, variable_info.type])
    constraint_declare = [["constraint", constraint.as_list()]]
    sketch_declare = []
    for sketch in sketches:
        constraint_declare = _substitute_function_call(constraint_declare, sketch["func"].expr, sketch["func_call"])
        sketch_declare.append(["sketch", sketch["func"].expr, sketch["sketch"].as_list()])
    sl_result = []
    sl_result.extend(syn_declare)
    sl_result.extend(var_declare)
    sl_result.extend(constraint_declare)
    sl_result.extend(sketch_declare)
    #import pprint as pp
    #pp.pprint(sl_result)
    with open("mid.sl", "w") as oup:
        oup.write("\n".join(list(map(lambda x: _list_to_str(x), sl_result))))
    return sketches

def _substitute_function_call_semfix(constraint, function_name, symbolic_list, used_variable):
    #("constraint ", constraint)
    if type(constraint) != list:
        return constraint
    constraint = list(map(lambda x: _substitute_function_call_semfix(x, function_name,
                                                                     symbolic_list, used_variable),
                          constraint))
    #print(constraint)
    if constraint[0] == function_name:
        result = [constraint[0]]
        for name, _ in used_variable.items():
            try:
                pos = symbolic_list.index(name)
                result.append(constraint[pos + 1])
            except ValueError:
                result.append(name)
        return result
    else:
        return constraint


def trans_semfix(constraint_file, sketch_file):
    with open(constraint_file, "r") as f:
        all_inp = f.readlines()
    with open(sketch_file) as f:
        sketch_lines = f.readlines()
    assert len(all_inp) > 1
    symbolic_variable_list = all_inp[0].split(' ')
    all_inp = all_inp[1:]
    all_inp = list(map(lambda x: x.strip(), all_inp))
    all_inp = list(filter(lambda x: len(x) > 0, all_inp))
    sketches = []
    for i in range(0, len(sketch_lines)):
        left_sketch, sketch, right_sketch = sketch_translator.parse_sketch(sketch_lines[i])
        sketches.append({"left_sketch": left_sketch,
                         "sketch": sketch,
                         "right_sketch": right_sketch})
    constraint = _parse_constraint(" ".join(all_inp))
    private_variable_table = {}
    constant_table = {"Int": [], "Bool": []}
    operator_list = ["<", "<=", "and", "or", "not"]
    variable_table = {}
    constraint.simplify()
    for sketch in sketches:
        sketch["sketch"].simplify()

    _collect_used_component(constraint, variable_table, constant_table, operator_list)
    for sketch in sketches:
        sketch["private_variable"] = {}
        _collect_used_component(sketch["sketch"], variable_table, constant_table, operator_list, sketch["private_variable"])
        for private_name in sketch["private_variable"]:
            private_variable_table[private_name] = True

    for variable, variable_info in variable_table.items():
        if variable_info.type is None:
            variable_info.type = "Int"

    count = 0
    for sketch in sketches:
        count += 1
        sketch_name = "p" + str(count)
        if sketch["sketch"].type == "Assign":
            sketch["func"] = ExprInfo(sketch_name, sketch["sketch"].expr[1].type)
            sketch["sketch"] = sketch["sketch"].expr[2]
            sketch["left_sketch"] += sketch["func"].expr + " = "
        else:
            sketch["func"] = ExprInfo(sketch_name, "Bool")
    constraint = constraint.as_list()
    syn_declare = []
    for sketch in sketches:
        sub_variable_table = {}
        for name, var in variable_table.items():
            if name not in sketch["private_variable"] and name in private_variable_table:
                continue
            sub_variable_table[name] = var
        current_function_declare = _make_declare(sketch["func"], sub_variable_table, constant_table, operator_list)
        constraint = _substitute_function_call_semfix(constraint, sketch["func"].expr, symbolic_variable_list, sub_variable_table)
        syn_declare.append(current_function_declare)
        arg_list = current_function_declare[2]
        sketch["func_call"] = [sketch["func"]]
        sketch["func_call"].extend(list(map(lambda x: x[0], arg_list)))
    var_declare = []
    for name, variable_info in variable_table.items():
        var_declare.append(["declare-var", variable_info.expr, variable_info.type])
    constraint_declare = [["constraint", constraint]]
    sketch_declare = []
    for sketch in sketches:
        sketch_declare.append(["sketch", sketch["func"].expr, sketch["sketch"].as_list()])
    sl_result = []
    sl_result.extend(syn_declare)
    sl_result.extend(var_declare)
    sl_result.extend(constraint_declare)
    sl_result.extend(sketch_declare)
    #import pprint as pp
    #pp.pprint(sl_result)
    with open("mid.sl", "w") as oup:
        oup.write("\n".join(list(map(lambda x: _list_to_str(x), sl_result))))
    return sketches

def trans(constraint_file, sketch_file):
    if config.is_semfix:
        return trans_semfix(constraint_file, sketch_file)
    else:
        return trans_normal_klee(constraint_file, sketch_file)

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