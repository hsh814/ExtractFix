import z3
import config
from util import operators
from util.common import new_variable, build_only_one

_node_count = 0

class Node:
    def __init__(self, none_term_name, sketch, depth, function):
        none_term_info = function.none_term[none_term_name]
        rules = none_term_info.rules
        global _node_count
        _node_count += 1
        self.id = _node_count
        self.operators = []
        self.terminals = []
        self.operator_indicators = []
        self.terminal_indicators = []
        self.subtree_list = {}
        self.sketch = sketch
        self.info = none_term_info
        self.is_death = False
        self.used_var = None
        for rule in rules:
            if type(rule) == str or type(rule) == tuple:
                self.terminals.append(rule)
            else:
                self.operators.append(rule)
                subexpr_count = {}
                for name in rule[1:]:
                    if name in function.none_term:
                        if name not in subexpr_count:
                            subexpr_count[name] = 0
                        subexpr_count[name] += 1
                        if name not in self.subtree_list:
                            self.subtree_list[name] = []
                        if subexpr_count[name] > len(self.subtree_list[name]):
                            self.subtree_list[name].append(None)
        if depth > config.depth:
            self.subtree_list = {}
            self.operators = []
        if sketch and type(sketch) == list:
            operator = sketch[0]
            #print(sketch, operator)
            for rule in rules:
                if type(rule) == list and rule[0] == operator:
                    #print("satisfy", rule)
                    subexpr_count = {}
                    for (pos, name) in enumerate(rule[1:]):
                        if name in function.none_term:
                            if name not in subexpr_count:
                                subexpr_count[name] = 0
                            #print(name, subexpr_count[name], len(self.subtree_list[name]))
                            self.subtree_list[name][subexpr_count[name]] = \
                                Node(name, sketch[pos+1], 0, function)
                            subexpr_count[name] += 1
        for name in self.subtree_list.keys():
            for i in range(len(self.subtree_list[name])):
                if self.subtree_list[name][i] == None:
                    self.subtree_list[name][i] = Node(name, None, depth+1, function)
        for name in self.subtree_list.keys():
            self.subtree_list[name] = list(filter(lambda x: not x.is_death, self.subtree_list[name]))
        for (i, operator) in enumerate(self.operators):
            subexpr_count = {}
            is_valid = True
            for subexpr in operator[1:]:
                if subexpr not in subexpr_count:
                    subexpr_count[subexpr] = 0
                subexpr_count[subexpr] += 1
                if subexpr_count[subexpr] > len(self.subtree_list[subexpr]):
                    is_valid = False
                    break
            if not is_valid:
                self.operators[i] = None
        self.operators = list(filter(lambda x: x, self.operators))
        for _ in range(len(self.operators)):
            self.operator_indicators.append(new_variable("Bool"))
        for _ in range(len(self.terminals)):
            self.terminal_indicators.append(new_variable("Bool"))
        if len(self.operators) == 0 and len(self.terminals) == 0:
            self.is_death = True
        else:
            self.used_var = new_variable("Bool")

    def print_tree(self):
        print("id:", self.id, "symbol:", self.info.name, "sketch:", self.sketch)
        for symbol, subtrees in self.subtree_list.items():
            print(symbol, ":", " ".join(list(map(lambda x: str(x.id), subtrees))))
        for symbol, subtrees in self.subtree_list.items():
            for subtree in subtrees:
                subtree.print_tree()

    def get_structure_constraint(self, soft_list, hard_list, is_root=False):
        assert not self.is_death
        if is_root:
            hard_list.append(self.used_var)
        elif self.sketch:
            soft_list.append(self.used_var)
        else:
            soft_list.append(z3.Not(self.used_var))
        indicators = []
        for var in self.terminal_indicators: indicators.append(var)
        for var in self.operator_indicators: indicators.append(var)
        build_only_one(indicators, hard_list, self.used_var)
        if self.sketch:
            if type(self.sketch) == list:
                sketch_operator = self.sketch[0]
                for (i, operator) in enumerate(self.operators):
                    if operator[0] == sketch_operator:
                        soft_list.append(self.operator_indicators[i])
            else:
                for (i, terminal) in enumerate(self.terminals):
                    if terminal == self.sketch:
                        soft_list.append(self.terminal_indicators[i])
        for (i, operator) in enumerate(self.operators):
            used_list = []
            subexpr_count = {}
            for subexpr in operator[1:]:
                if subexpr not in subexpr_count:
                    subexpr_count[subexpr] = 0
                subtree_used = self.subtree_list[subexpr][subexpr_count[subexpr]].used_var
                used_list.append(subtree_used)
                subexpr_count[subexpr] += 1
            for symbol, subtrees in self.subtree_list.items():
                used_count = 0
                if symbol in subexpr_count:
                    used_count = subexpr_count[symbol]
                for subtree in subtrees[used_count:]:
                    used_list.append(z3.Not(subtree.used_var))
            hard_list.append(z3.Implies(self.operator_indicators[i], z3.And(used_list)))
        all_used = []
        for symbol, subtrees in self.subtree_list.items():
            for subtree in subtrees:
                all_used.append(z3.Not(subtree.used_var))
        for indicator in self.terminal_indicators:
            hard_list.append(z3.Implies(indicator, z3.And(all_used)))
        for symbol, subtrees in self.subtree_list.items():
            for subtree in subtrees:
                subtree.get_structure_constraint(soft_list, hard_list)

    def get_io_constraint(self, input, hard_list):
        current_type = self.info.type
        return_value = new_variable(current_type)
        for (i, terminal) in enumerate(self.terminals):
            if type(terminal) == tuple:
                hard_list.append(z3.Implies(self.terminal_indicators[i],
                                            return_value == terminal[1]))
            else:
                hard_list.append(z3.Implies(self.terminal_indicators[i],
                                            return_value == input[terminal]))
        subtree_result = {}
        for (symbol, subtrees) in self.subtree_list.items():
            subtree_result[symbol] = []
            for subtree in subtrees:
                subtree_result[symbol].append(subtree.get_io_constraint(input, hard_list))
        for (i, operator) in enumerate(self.operators):
            subexpr_values = []
            symbol_count = {}
            for subexpr in operator[1:]:
                if subexpr not in symbol_count: symbol_count[subexpr] = 0
                subexpr_values.append(subtree_result[subexpr][symbol_count[subexpr]])
                symbol_count[subexpr] += 1
            hard_list.append(z3.Implies(self.operator_indicators[i],
                                        return_value == operators.string2z3[operator[0]](subexpr_values)))
        return return_value

    def parse_output(self, model):
        assert z3.is_true(model[self.used_var])
        for (i, terminal) in enumerate(self.terminals):
            if z3.is_true(model[self.terminal_indicators[i]]):
                return terminal
        for (i, operator) in enumerate(self.operators):
            if z3.is_true(model[self.operator_indicators[i]]):
                subexpr_count = {}
                result = [operator[0]]
                for subexpr in operator[1:]:
                    if subexpr not in subexpr_count:
                        subexpr_count[subexpr] = 0
                    result.append(self.subtree_list[subexpr][subexpr_count[subexpr]].parse_output(model))
                    subexpr_count[subexpr] += 1
                return result
        assert False

class FunctionTree:

    def __init__(self, function):
        self.root = Node("Start", function.sketch, 0, function)
        #self.root.print_tree()

    def get_structure_constraint(self, hard_cons_list, soft_cons_list):
        self.root.get_structure_constraint(soft_cons_list, hard_cons_list, True)

    def get_o(self, input, hard_cons_list):
        return self.root.get_io_constraint(input, hard_cons_list)

    def get_io_constraint(self, input, output, hard_cons_list):
        hard_cons_list.append(self.get_o(input, hard_cons_list) == output)

