import z3
from util import common, synthesis
import config

def filter(candidate, task):
    all_variable = []
    for name, var in task.variable_list.items():
        all_variable.append(var)
    if len(task.constraint) > 1:
        return None
    constraint = task.constraint[0]
    if constraint[0] != "=>":
        return None
    constraint = constraint[1]
    for i in range(len(candidate)):
        candidate[i] = candidate[i]
    solver = z3.Solver()
    for i in range(len(candidate)):
        for j in range(i):
            solver.push()
            inp = common.get_new_symbolic_input(all_variable)
            solver.add(synthesis.parse_constraint_with_function_and_input(constraint, candidate[i], task, inp) !=
                       synthesis.parse_constraint_with_function_and_input(constraint, candidate[j], task, inp))
            result = solver.check()
            if result == z3.unsat:
                solver.pop()
                return None
            solver.pop()

    while True:
        if len(candidate) == 1:
            return candidate[0]
        '''print("rem")
        for function_list in candidate:
            print(function_list)'''
        value = [0] * len(candidate)
        solver.push()
        indicator_list = []
        symbolic = common.get_new_symbolic_input(all_variable)
        for i, function_list in enumerate(candidate):
            indicator = common.new_variable("Bool")
            solver.add(indicator == synthesis.parse_constraint_with_function_and_input(
                constraint, function_list, task, symbolic))
            indicator_list.append(indicator)
        constraint_list = []
        for i in range(len(candidate)):
            for j in range(i):
                constraint_list.append(indicator_list[i] != indicator_list[j])
        solver.add(z3.Or(constraint_list))
        for _ in range(config.filter_example):
            result = solver.check()
            if result == z3.unsat:
                break
            model = solver.model()
            inp = common.parse_input_from_model(all_variable, symbolic, model)
            for i in range(len(candidate)):
                if z3.is_true(model[indicator_list[i]]):
                    value[i] += 1
            constraint_list = []
            for name, var in symbolic.items():
                constraint_list.append(var != inp[name])
            solver.add(z3.Or(constraint_list))
        solver.pop()
        pos = 0
        for i, val in enumerate(value):
            if val < value[pos]:
                pos = i
        #print(value, pos)
        new_candidate_list = candidate[:pos]
        new_candidate_list.extend(candidate[pos+1:])
        candidate = new_candidate_list

