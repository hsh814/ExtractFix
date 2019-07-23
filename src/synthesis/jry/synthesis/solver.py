from synthesis import buildtree
from parser import task
from util import common, operators, synthesis
import z3
import config
import pprint as pp

class Solver:
    def solve(self, task):
        assert False

class SyntaxSolver(Solver):
    def solve(self, task):
        hard_list = []
        soft_list = []
        for function_name, function_tree in task.function_tree_list.items():
            function_tree.get_structure_constraint(hard_list, soft_list)
            function_tree.get_heuristic_constraint(hard_list, soft_list)
        solver = z3.Solver()
        solver.set(unsat_core=True)
        step = 0
        all_result = []
        while True:
            step += 1
            while True:
                solver.push()
                for (pos, constraint) in enumerate(hard_list):
                    solver.assert_and_track(constraint, "hard" + str(pos))
                for (pos, constraint) in enumerate(soft_list):
                    solver.assert_and_track(constraint, "soft" + str(pos))
                result = solver.check()
                if result == z3.sat:
                    model = solver.model()
                    function_result_list = {}
                    for function_name, function_tree in task.function_tree_list.items():
                        function_result_list[function_name] = function_tree.parse_output(model)
                    solver.pop()
                    break
                unsat_core = solver.unsat_core()
                solver.pop()
                relax_list = []
                for i in range(len(soft_list)):
                    if z3.Bool("soft" + str(i)) in unsat_core:
                        relax_var = common.new_variable("Bool")
                        relax_list.append(relax_var)
                        soft_list[i] = z3.Or(soft_list[i], relax_var)
                if len(relax_list) == 0:
                    return all_result
                common.build_only_one(relax_list, hard_list)

            solver.push()
            constraint_list = []
            for constraint in task.constraint:
                constraint_list.append(synthesis.parse_constraint_with_function(constraint, function_result_list, task))
            solver.add(z3.Not(z3.And(constraint_list)))
            result = solver.check()
            if result == z3.unsat:
                solver.pop()
                all_result.append(function_result_list)
                #print("find", function_result_list)
                if len(all_result) >= config.result_num:
                    return all_result
                #hard_list.extend(soft_list)
                #soft_list = []
                function_constraint_list = []
                for function_name, function_info in task.function_list.items():
                    function_tree = task.function_tree_list[function_name]
                    current_expression = function_result_list[function_name]
                    inp = common.get_new_symbolic_input(function_info.arg_list)
                    function_constraint_list.append(function_tree.get_o(inp, hard_list) !=
                                                    synthesis.parse_function_with_input(current_expression, inp))
                hard_list.append(z3.Or(function_constraint_list))
                continue

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
            synthesis.parse_constraint_with_input(task, point, hard_list)
            solver.pop()

class SemanticsSolver(Solver):
    def _better_cons(self, standard, oup1, oup2, return_type):
        if return_type == "Bool":
            return (standard == oup1) and (standard != oup2)
        elif return_type == "Int":
            return z3.If(standard < oup1, oup1 - standard, standard - oup1) < \
                   z3.If(standard < oup2, oup2 - standard, standard - oup2)
        else:
            assert False

    def _get_new_candidate(self, task, candidate_list):
        solver = z3.Solver()
        hard_list = []
        soft_list = []
        for function_name, function_info in task.function_list.items():
            function_tree = task.function_tree_list[function_name]
            function_tree.get_structure_constraint(hard_list, soft_list)
            soft_list = []
            function_tree.get_heuristic_constraint(hard_list, soft_list)
            hard_list.extend(soft_list)
        symbol_input_list = []
        for candidate in candidate_list:
            oup_list = []
            current_input = {}
            for function_name, function_expr in candidate.items():
                function_info = task.function_list[function_name]
                function_tree = task.function_tree_list[function_name]
                symbolic_inp = common.get_new_symbolic_input(function_info.arg_list)
                current_input[function_name] = symbolic_inp
                oup1 = function_tree.get_o(symbolic_inp, hard_list)
                oup2 = synthesis.parse_function_with_input(function_expr, symbolic_inp)
                standard = synthesis.parse_function_with_input(function_info.sketch, symbolic_inp)
                oup_list.append(self._better_cons(standard, oup1, oup2, function_info.return_type))
            #print(oup_list)
            hard_list.append(z3.Or(oup_list))
            symbol_input_list.append(current_input)
        solver.add(z3.And(hard_list))
        checker = z3.Solver()
        while True:
            solver.push()
            result = solver.check()
            if result == z3.unsat:
                solver.pop()
                return None
            model = solver.model()
            solver.pop()
            function_result = {}
            for function_name, function_tree in task.function_tree_list.items():
                function_result[function_name] = function_tree.parse_output(model)
            for (i, candidate) in enumerate(candidate_list):
                flag = False
                symbolic_inputs = symbol_input_list[i]
                for function_name, function_info in task.function_list.items():
                    inp = common.parse_input_from_model(function_info.arg_list,
                                                        symbolic_inputs[function_name], model)
                    oup2 = synthesis.parse_function_with_input(candidate[function_name], inp, False)
                    oup1 = synthesis.parse_function_with_input(function_result[function_name], inp, False)
                    standard = synthesis.parse_function_with_input(function_info.sketch, inp, False)
                    if function_info.return_type == "Bool":
                        if oup1 == standard and oup2 != standard:
                            flag = True
                    else:
                        assert function_info.return_type == "Int"
                        if abs(oup1 - standard) < abs(oup2 - standard):
                            flag = True
                assert flag
            checker.push()
            constraint_list = []
            for constraint in task.constraint:
                constraint_list.append(synthesis.parse_constraint_with_function(
                    constraint, function_result, task))
            checker.add(z3.Not(z3.And(constraint_list)))
            result = checker.check()
            if result == z3.unsat:
                checker.pop()
                return function_result
            model = checker.model()
            checker.pop()
            point = {}
            for (name, var) in task.variable_list.items():
                result = model[var.z3_var]
                if result is None:
                    point[name] = common.get_random(var.type)
                elif var.type == "Int":
                    point[name] = result.as_long()
                elif var.type == "Bool":
                    point[name] = z3.is_true(result)
            print("new point", point)
            print(function_result)
            hard_list = []
            synthesis.parse_constraint_with_input(task, point, hard_list)
            solver.add(z3.And(hard_list))

    def solve(self, task):
        config.result_num = 1
        pre_solver = SyntaxSolver()
        candidate_list = pre_solver.solve(task)
        assert len(candidate_list) == 1
        print("first", candidate_list[0])
        while True:
            new_candidate = self._get_new_candidate(task, candidate_list)
            if new_candidate is None:
                return candidate_list
            print("new candidate:", new_candidate)
            candidate_list.append(new_candidate)