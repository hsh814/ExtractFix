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
                hard_list.extend(soft_list)
                soft_list = []
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

'''class SemanticsSolver(Solver):
    def _get_points(self, function_info, function_tree):
        solver = z3.Solver()
        hard_list = []
        soft_list = []
        function_tree.get_structure_constraint(hard_list, soft_list)
        points_list = []
        for hard_cons in hard_list:
            solver.add(hard_cons)
        while True:
            solver.push()
            result = solver.check()
            assert result == z3.sat
            model = solver.model()
            result_function = function_tree.parse_output(model)
            print(result_function)
            for inp, oup in points_list:
                print(inp, oup, synthesis.parse_function_with_input(result_function, inp, False))
                assert synthesis.parse_function_with_input(result_function, inp, False) == oup
            solver.pop()
            inp = common.get_new_symbolic_input(function_info.arg_list)
            solver.push()
            hard_list = []
            solver.add(function_tree.get_o(inp, hard_list) !=
                       synthesis.parse_function_with_input(result_function, inp))
            for hard_cons in hard_list:
                solver.add(hard_cons)
            result = solver.check()
            if result == z3.unsat:
                print("finish")
                print(result_function)
                print(points_list)
                checker = z3.Solver()
                checker.add(synthesis.parse_function_with_input(result_function, inp) !=
                            synthesis.parse_function_with_input(function_info.sketch, inp))
                assert checker.check() == z3.unsat
                return points_list
            model = solver.model()
            solver.pop()
            counter_example = common.parse_input_from_model(function_info.arg_list, inp, model)
            oup = synthesis.parse_function_with_input(function_info.sketch, counter_example)
            points_list.append([counter_example, oup])
            hard_list = []
            function_tree.get_io_constraint(counter_example, oup, hard_list)
            for hard_cons in hard_list:
                solver.add(hard_cons)


    def solve(self, task):
        solve = z3.Solver()
        hard_list = []
        soft_list = []
        points_table = {}
        for function_name, function_info in task.function_list.items():
            points_table[function_name] = self._get_points(function_info, task.function_tree_list[function_name])
        exit(0)'''