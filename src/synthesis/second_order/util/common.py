import z3
import random

special_var_table = {}

_var_count = 0
def new_variable(var_type):
    global _var_count
    _var_count += 1
    if var_type == "Bool":
        return z3.Bool("Bool" + str(_var_count))
    elif var_type == "Int":
        return z3.Int("Int" + str(_var_count))
    else:
        assert False

def _recursively_build_only_one(variable_list, constraint_list):
    if len(variable_list) == 1:
        return variable_list[0]
    mid = len(variable_list) // 2
    left = _recursively_build_only_one(variable_list[:mid], constraint_list)
    right = _recursively_build_only_one(variable_list[mid:], constraint_list)
    constraint_list.append(z3.Not(z3.And(left, right)))
    return_value = new_variable("Bool")
    constraint_list.append(return_value == z3.Or(left, right))
    return return_value

def build_only_one(variable_list, constraint_list, one_value=True):
    assert len(variable_list) > 0
    result = _recursively_build_only_one(variable_list, constraint_list)
    constraint_list.append(result == one_value)

def get_random(variable_type):
    if variable_type == "Int":
        return random.randint(-10 ** 8, 10 ** 8)
    elif variable_type == "Bool":
        return random.randint(0, 1) == 0
    else:
        assert False

def _list_to_string(expr):
    if type(expr) == str:
        return expr
    if type(expr) == tuple:
        return str(expr[1])
    if type(expr) == list:
        string_expr = list(map(lambda x: _list_to_string(x), expr))
        return "(" + " ".join(string_expr) + ")"
    assert False

def print_function(function_result, function_info):
    arg_list = list(map(lambda x: [x.name, x.type], function_info.arg_list))
    result = ["define-fun", function_info.name, arg_list, function_info.return_type, function_result]
    print(_list_to_string(result))

def get_new_symbolic_input(input_list):
    inp = {}
    for var in input_list:
        variable_name = var.name
        variable_type = var.type
        inp[variable_name] = new_variable(variable_type)
    return inp

def parse_input_from_model(arg_list, symbolic_inp, model):
    inp = {}
    for var_info in arg_list:
        symbolic_var = symbolic_inp[var_info.name]
        if model[symbolic_var] is not None:
            if var_info.type == "Int":
                inp[var_info.name] = model[symbolic_var].as_long()
            elif var_info.type == "Bool":
                inp[var_info.name] = z3.is_true(model[symbolic_var])
            else:
                assert False
        else:
            inp[var_info.name] = get_random(var_info.type)
    return inp
