import sys
sys.path.append("/Users/pro/Desktop/work/2019S/z3/build/python")
import z3
import copy

_variable_count = 0
def _new_variable(type):
    global _variable_count
    _variable_count += 1
    if type == "Bool":
        return z3.Bool("variable" + str(_variable_count))
    elif type == "Int":
        return z3.Int("variable" + str(_variable_count))
    else:
        assert False

def _build_structure(list, constraint_list):
    first = _new_variable("Bool")
    second = _new_variable("Bool")
    if len(list) == 2:
        constraint_list.append(first == z3.Or(list))
        constraint_list.append(second == z3.And(list))
    elif len(list) == 3:
        Lfirst, Lsecond = _build_structure(list[:2], solver)
        constraint_list.append(first == z3.Or(Lfirst, list[2]))
        constraint_list.append(second == z3.Or(z3.And(Lfirst, list[2]), Lsecond))
    else:
        mid = len(list) // 2
        Lfirst, Lsecond = _build_structure(list[:mid], solver)
        Rfirst, Rsecond = _build_structure(list[mid:], solver)
        constraint_list.append(first == z3.Or(Lfirst, Rfirst))
        constraint_list.append(second == z3.Or(z3.And(Lfirst, Rfirst), Lsecond, Rsecond))
    return first, second

class maxSMT:
    def __init__(self):
        self.hard = []
        self.soft = []
        self.solver = z3.Solver()
        self.model = None
        self.solver.set(unsat_core=True)
        self.cost = 0

    def add(self, contraint):
        self.hard.append(contraint)

    def add_soft(self, constraint):
        self.soft.append(constraint)

    def get_model(self):
        return self.model

    def check(self):
        ans = 0
        allRelaxVar = []
        current_soft = copy.copy(self.soft)
        current_hard = copy.copy(self.hard)
        while True:
            #print("turn", ans)
            #import pprint as pp
            #pp.pprint(current_soft)
            #pp.pprint(current_hard)
            self.solver.push()
            for (id, constraint) in enumerate(current_hard):
                self.solver.assert_and_track(constraint, "hard" + str(id))
            for (id, constraint) in enumerate(current_soft):
                self.solver.assert_and_track(constraint, "soft" + str(id))
            relaxVariableList = []
            if self.solver.check() == z3.sat:
                self.model = self.solver.model()
                #print(self.model, allRelaxVar)
                count = 0
                for var in allRelaxVar:
                    if z3.is_true(self.model[var]):
                        count += 1
                        #print("relax true", var)
                #print(ans, count)
                #print(allRelaxVar)
                assert count == ans
                self.cost = ans
                self.solver.pop()
                return z3.sat
            ans += 1
            unsatCore = self.solver.unsat_core()
            self.solver.pop()
            for i in range(len(current_soft)):
                if z3.Bool("soft" + str(i)) in unsatCore:
                    relaxVariable = _new_variable("Bool")
                    current_soft[i] = z3.Or(relaxVariable, current_soft[i])
                    relaxVariableList.append(relaxVariable)
            allRelaxVar.extend(relaxVariableList)
            if len(relaxVariableList) == 0:
                return z3.unsat
            if len(relaxVariableList) == 1:
                current_hard.append(relaxVariableList[0])
                continue
            first, second = _build_structure(relaxVariableList, current_hard)
            current_hard.append(first)
            current_hard.append(z3.Not(second))


if __name__ == "__main__":
    solver = maxSMT()
    x = z3.Int("x")
    y = z3.Int("y")
    z = z3.Int("z")
    solver.add_soft(x == y)
    solver.add_soft(x == z)
    solver.add_soft(y == z)
    solver.add_soft(y == z)
    solver.add_soft(x != z)
    solver.add_soft(x != y)
    solver.add_soft(y != z)
    solver.check()
    #print(solver.get_model())
    print(solver.cost)
