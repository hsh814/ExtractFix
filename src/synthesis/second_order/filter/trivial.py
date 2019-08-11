from util import common, synthesis
import config
import z3

def filter(candidates, task):
    while True:
        #print("filter")
        #for candidate in candidates:
        #    print(candidate)
        if len(candidates) == 1:
            return candidates[0]
        value = [0] * len(candidates)
        for function_name, function_info in task.function_list.items():
            solver = z3.Solver()
            symbolic_inp = common.get_new_symbolic_input(function_info.arg_list)
            indicators = []
            for (i, candidate) in enumerate(candidates):
                indicator = common.new_variable(function_info.return_type)
                solver.add(indicator == synthesis.parse_function_with_input(candidate[function_name], symbolic_inp))
                indicators.append(indicator)
            constraint_list = []
            for (i, indicator1) in enumerate(indicators):
                for indicator2 in indicators[:i]:
                    constraint_list.append(indicator1 != indicator2)
            solver.add(z3.Or(constraint_list))
            for _ in range(config.filter_example):
                solver.push()
                result = solver.check()
                if result == z3.unsat:
                    solver.pop()
                    break
                inp = common.parse_input_from_model(function_info.arg_list, symbolic_inp, solver.model())
                #print(inp)
                solver.pop()
                standard = synthesis.parse_function_with_input(function_info.sketch, inp, False)
                for i in range(len(candidates)):
                    current_oup = synthesis.parse_function_with_input(candidates[i][function_name], inp, False)
                    if function_info.return_type == "Int":
                        value[i] += abs(current_oup - standard)
                    elif function_info.return_type == "Bool":
                        if current_oup != standard:
                            value[i] += 1
                    else:
                        assert False
                constraint_list = []
                for name, var in symbolic_inp.items():
                    constraint_list.append(var != inp[name])
                solver.add(z3.Or(constraint_list))
        #print(value)
        pos = 0
        for i, cost in enumerate(value):
            if cost > value[pos]:
                pos = i
        new_candidates = []
        for (i, candidate) in enumerate(candidates):
            if i != pos:
                new_candidates.append(candidate)
        candidates = new_candidates