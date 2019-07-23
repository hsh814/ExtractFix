from util import common, operators
import z3

def parse_constraint(constraint, parsed_list, task, inp, hard_list):
    if type(constraint) == tuple:
        if constraint[0] == "Int":
            return int(constraint[1])
        elif constraint[0] == "Bool":
            return constraint[1]
        else:
            assert False
    if type(constraint) == str:
        assert constraint in task.variable_list
        if constraint in inp:
            return inp[constraint]
        return common.get_random(task.variable_list[constraint].type)
    if type(constraint) == list:
        operator = constraint[0]
        if operator in task.function_list.keys():
            function_tree = task.function_tree_list[operator]
            function_info = task.function_list[operator]
            arg = list(map(lambda x: parse_constraint(x, parsed_list, task, inp, hard_list),
                           constraint[1:]))
            id = operator + str(arg)
            if id in parsed_list:
                return parsed_list[id]
            return_variable = common.new_variable(function_info.return_type)
            function_inp = {}
            for (i, var) in enumerate(function_info.arg_list):
                function_inp[var.name] = arg[i]
            function_tree.get_io_constraint(function_inp, return_variable, hard_list)
            parsed_list[id] = return_variable
            return return_variable
        elif operator in operators.string2z3:
            arg = list(map(lambda x: parse_constraint(x, parsed_list, task, inp, hard_list),
                           constraint[1:]))
            return operators.string2z3[operator](arg)
        else:
            assert False
    assert False

def parse_function_with_input(expression, inp, is_symbolic=True):
    if type(expression) == tuple:
        if expression[0] == "Int":
            return int(expression[1])
        elif expression[0] == "Bool":
            return expression[1]
        else:
            assert False
    if type(expression) == str:
        assert expression in inp
        return inp[expression]
    if type(expression) == list:
        operator = expression[0]
        arg = list(map(lambda x: parse_function_with_input(x, inp, is_symbolic), expression[1:]))
        if is_symbolic:
            return operators.string2z3[operator](arg)
        else:
            return operators.string2python[operator](arg)
    assert False

def parse_constraint_with_function_and_input(constraint, function_list, task, symbolic_inp):
    #print("_parse_constraint_with_function", constraint)
    if type(constraint) == tuple:
        if constraint[0] == "Int":
            return int(constraint[1])
        elif constraint[0] == "Bool":
            return constraint[1]
        else:
            assert False
    if type(constraint) == str:
        #(task.variable_list)
        assert constraint in task.variable_list
        return symbolic_inp[constraint]
    if type(constraint) == list:
        operator = constraint[0]
        arg = list(map(lambda x: parse_constraint_with_function(x, function_list, task),
                       constraint[1:]))
        if operator in task.function_list.keys():
            function_info = task.function_list[operator]
            function_value = function_list[operator]
            function_arg = {}
            for (i, var) in enumerate(function_info.arg_list):
                function_arg[var.name] = arg[i]
            return parse_function_with_input(function_value, function_arg)
        else:
            return operators.string2z3[operator](arg)
    assert False

def parse_constraint_with_function(constraint, function_list, task):
    var_table = {}
    for name, var in task.variable_list.items():
        var_table[name] = var.z3_var
    return parse_constraint_with_function_and_input(constraint, function_list, task, var_table)

def parse_constraint_with_input(task, inp, hard_list):
    constraints = task.constraint
    parsed_list = {}
    constraint_list = []
    for constraint in constraints:
        constraint_list.append(parse_constraint(constraint, parsed_list, task, inp, hard_list))
    hard_list.append(z3.And(constraint_list))