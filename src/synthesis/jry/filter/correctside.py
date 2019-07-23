from util import common, synthesis, operators
import config
import z3

def _get_cost(oup1, oup2):
    assert type(oup1) == type(oup2)
    if type(oup1) == type(1):
        return abs(oup1 - oup2)
    elif type(oup1) == type(False):
        return 0 if oup1 == oup2 else 1
    else:
        assert False

def _get_all_function_call(expr, inp, is_symbolic, candidate, result_list, task):
    #print(expr)
    if type(expr) == tuple:
        if expr[0] == "Int":
            return int(expr[1])
        elif expr[1] == "Bool":
            return expr[1]
        else:
            assert False
    if type(expr) == str:
        assert expr in inp
        return inp[expr]
    if type(expr) == list:
        operator = expr[0]
        arg = list(map(lambda x: _get_all_function_call(x, inp, is_symbolic, candidate,
                                                        result_list, task), expr[1:]))
        if operator in candidate:
            new_inp = {}
            function_info = task.function_list[operator]
            for (i, var) in enumerate(function_info.arg_list):
                new_inp[var.name] = arg[i]
            result = synthesis.parse_function_with_input(candidate[operator], new_inp, is_symbolic)
            result_list.append(result)
            return result
        else:
            assert operator in operators.string2python
            if is_symbolic:
                return operators.string2z3[operator](arg)
            else:
                return operators.string2python[operator](arg)
    assert False


def filter(candidates, task):
    while True:
        #print("filter")
        if len(candidates) == 1:
            return candidates[0]
        value = [0] * len(candidates)
        sketch_table = {}
        for function_name, function_info in task.function_list.items():
            sketch_table[function_name] = function_info.sketch

        points = []
        for _ in range(config.filter_example):
            solver = z3.Solver()
            symbolic_inp = common.get_new_symbolic_input(task.variable_list.values())
            constraint_list = []
            for constraint in task.constraint:
                constraint_list.append(synthesis.parse_constraint_with_function_and_input(
                    constraint, sketch_table, task, symbolic_inp
                ))
            for point in points:
                diff_cons = []
                for name, var in symbolic_inp:
                    diff_cons.append(var != point[name])
                solver.add(z3.Or(diff_cons))
            solver.add(z3.And(constraint_list))
            candidate_function_call_list = []
            for candidate in candidates:
                function_call_list = []
                for constraint in task.constraint:
                    #print(constraint)
                    _get_all_function_call(constraint, symbolic_inp, True, candidate,
                                           function_call_list, task)
                candidate_function_call_list.append(function_call_list)
                #print(candidate, function_call_list)
            diff_cons = []
            for i in range(len(candidates)):
                for j in range(i):
                    assert len(candidate_function_call_list[i]) == len(candidate_function_call_list[j])
                    for k in range(len(candidate_function_call_list[i])):
                        diff_cons.append(candidate_function_call_list[i][k] !=
                                         candidate_function_call_list[j][k])
            solver.add(z3.Or(diff_cons))
            solver.push()
            result = solver.check()
            if result == z3.unsat:
                solver.pop()
                break
            model = solver.model()
            solver.pop()
            inp = common.parse_input_from_model(task.variable_list.values(), symbolic_inp, model)
            #print(inp)
            standard_list = []
            for constraint in task.constraint:
                _get_all_function_call(constraint, inp, False, sketch_table, standard_list, task)
            #print(standard_list)
            for (i, candidate) in enumerate(candidates):
                result_list = []
                for constraint in task.constraint:
                    _get_all_function_call(constraint, inp, False, candidate, result_list, task)
                assert len(standard_list) == len(result_list)
                for (j, result) in enumerate(result_list):
                    value[i] += _get_cost(result, standard_list[j])
                #print(candidate, result_list)
        pos = 0
        for i, cost in enumerate(value):
            if cost > value[pos]:
                pos = i
        new_candidates = []
        for (i, candidate) in enumerate(candidates):
            if i != pos:
                new_candidates.append(candidate)
        candidates = new_candidates