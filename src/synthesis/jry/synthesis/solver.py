from synthesis import buildtree
from parser import task
from util import common, operators
import z3
import pprint as pp

def _parse_constraint(constraint, parsed_list, task, inp, hard_list):
    if type(constraint) == tuple:
        assert constraint[0] == "Int"
        return int(constraint[1])
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
            arg = list(map(lambda x: _parse_constraint(x, parsed_list, task, inp, hard_list),
                           constraint[1:]))
            id = operator + str(arg)
            if id in parsed_list:
                return parsed_list[id]
            return_variable = common.new_variable(function_info.return_type)
            function_inp = {}
            for (i, var) in enumerate(function_info.arg_list):
                function_inp[var.name] = arg[i]
            #for (i, var) in function_info.arg_table.items():
            #    function_inp[var.name] = arg[i]
            function_tree.get_io_constraint(function_inp, return_variable, hard_list)
            parsed_list[id] = return_variable
            return return_variable
        elif operator in operators.string2z3:
            arg = list(map(lambda x: _parse_constraint(x, parsed_list, task, inp, hard_list),
                           constraint[1:]))
            return operators.string2z3[operator](arg)
        else:
            assert False
    assert False

def _parse_function_with_input(expression, inp):
    #print("_parse_function_with_input", expression)
    if type(expression) == tuple:
        assert expression[0] == "Int"
        return int(expression[1])
    if type(expression) == str:
        assert expression in inp
        return inp[expression]
    if type(expression) == list:
        operator = expression[0]
        arg = list(map(lambda x: _parse_function_with_input(x, inp), expression[1:]))
        return operators.string2z3[operator](arg)
    assert False

def _parse_constraint_with_function(constraint, function_list, task):
    #print("_parse_constraint_with_function", constraint)
    if type(constraint) == tuple:
        assert constraint[0] == "Int"
        return int(constraint[1])
    if type(constraint) == str:
        #(task.variable_list)
        assert constraint in task.variable_list
        return task.variable_list[constraint].z3_var
    if type(constraint) == list:
        operator = constraint[0]
        arg = list(map(lambda x: _parse_constraint_with_function(x, function_list, task),
                       constraint[1:]))
        if operator in task.function_list.keys():
            function_info = task.function_list[operator]
            function_value = function_list[operator]
            function_arg = {}
            for (i, var) in enumerate(function_info.arg_list):
                function_arg[var.name] = arg[i]
            return _parse_function_with_input(function_value, function_arg)
        else:
            return operators.string2z3[operator](arg)
    assert False

def parse_constraint_with_input(task, inp, hard_list):
    constraints = task.constraint
    parsed_list = {}
    constraint_list = []
    for constraint in constraints:
        constraint_list.append(_parse_constraint(constraint, parsed_list, task, inp, hard_list))
    hard_list.append(z3.And(constraint_list))

def synthesis(task):
    hard_list = []
    soft_list = []
    for function_name, function_tree in task.function_tree_list.items():
        function_tree.get_structure_constraint(hard_list, soft_list)
        function_tree.get_heuristic_constraint(hard_list, soft_list)
        #function_info = task.function_list[function_name]
        #arg_list = function_info.arg_list
        #symbolic_input1 = common.get_new_symbolic_input(arg_list)
        #symbolic_input2 = common.get_new_symbolic_input(arg_list)
        #hard_list = []
        #print(symbolic_input1)
        #print(symbolic_input2)
        #hard_list.append(function_tree.get_o(symbolic_input1, hard_list) !=
        #                 function_tree.get_o(symbolic_input2, hard_list))
        #pp.pprint(hard_list)
    #input()
    solver = z3.Solver()
    solver.set(unsat_core=True)
    step = 0
    while True:
        step += 1
        while True:
            solver.push()
            for (pos, constraint) in enumerate(hard_list):
                solver.assert_and_track(constraint, "hard" + str(pos))
            for (pos, constraint) in enumerate(soft_list):
                solver.assert_and_track(constraint, "soft" + str(pos))
            #print("start solve")
            result = solver.check()
            #print("end solve")
            if result == z3.sat:
                model = solver.model()
                function_result_list = {}
                for function_name, function_tree in task.function_tree_list.items():
                    #print("parse", function_name)
                    function_result_list[function_name] = function_tree.root.node_parse_output(model)
                solver.pop()
                break
            unsat_core = solver.unsat_core()
            #print("unsat", unsat_core)
            solver.pop()
            relax_list = []
            for i in range(len(soft_list)):
                if z3.Bool("soft" + str(i)) in unsat_core:
                    relax_var = common.new_variable("Bool")
                    relax_list.append(relax_var)
                    soft_list[i] = z3.Or(soft_list[i], relax_var)
            if len(relax_list) == 0:
                return -1
            common.build_only_one(relax_list, hard_list)
            #print("add cost")

        solver.push()
        constraint_list = []
        #print(function_result_list)
        for constraint in task.constraint:
            constraint_list.append(_parse_constraint_with_function(constraint, function_result_list, task))
        solver.add(z3.Not(z3.And(constraint_list)))
        #print("step", step)
        #print(function_result_list)
        #pp.pprint(constraint_list)
        #print(solver)
        #input()
        result = solver.check()
        if result == z3.unsat:
            solver.pop()
            task.set_result(function_result_list)
            return 0
        model = solver.model()
        point = {}
        for (name, var) in task.variable_list.items():
            result = model[var.z3_var]
            if result is None:
                point[name] = common.get_random(var.type)
            elif var.type == "Int":
                point[name] = result.as_long()
            elif var.type == "Bool":
                point[name] = z3.is_true(result)
        #print("counterexample", model)
        #print(point)
        #input()
        parse_constraint_with_input(task, point, hard_list)
        solver.pop()
