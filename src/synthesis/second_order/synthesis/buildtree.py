import z3
import config
from util import operators
from util.common import new_variable, build_only_one, get_new_symbolic_input, special_var_table

_node_count = 0

class Node:

    def __init__(self, none_term_name, sketch, depth, function, is_extra_root=False):
        none_term_info = function.none_term[none_term_name]
        rules = none_term_info.rules
        global _node_count
        _node_count += 1
        self.id = _node_count
        self.operators = []
        self.terminals = []
        self.symbol = none_term_name
        self.operator_indicators = []
        self.terminal_indicators = []
        self.subtree_list = {}
        self.sketch = sketch
        self.info = none_term_info
        self.is_death = False
        self.used_var = None
        self.is_extra_root = is_extra_root
        self.fixed_child = None
        self.result_var = None
        self.has_special = False
        for rule in rules:
            if type(rule) == str or type(rule) == tuple:
                if rule in special_var_table:
                    if sketch == rule:
                        self.has_special = True
                    else:
                        continue
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
        if is_extra_root:
            self.sketch = None
            if none_term_name not in self.subtree_list:
                self.subtree_list[none_term_name] = []
            if len(self.subtree_list[none_term_name]) == 0:
                self.subtree_list[none_term_name].append(None)
            if depth == -1:
                self.fixed_child = Node(none_term_name, sketch, depth+1, function)
            else:
                self.fixed_child = Node(none_term_name, sketch, depth+1, function, True)
            self.subtree_list[none_term_name][0] = self.fixed_child
            depth = 0
        elif sketch and type(sketch) == list:
            operator = sketch[0]
            for rule in rules:
                if type(rule) == list and rule[0] == operator:
                    if rule[0] == "=" and rule[1] == "StartBool": continue
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
        #print(self.subtree_list)
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
        if self.sketch is not None and "Start" in self.subtree_list:
            for subtree in self.subtree_list["Start"]:
                if subtree.has_special:
                    self.has_special = True
            if self.has_special:
                for name, subtree_list in self.subtree_list.items():
                    for subtree in subtree_list:
                        subtree.set_special()

    def set_special(self):
        if self.has_special or self.sketch is None:
            return
        for type, subtree_list in self.subtree_list.items():
            for subtree in self.subtree_list:
                subtree.set_speical()

    def print_tree(self):
        print("id:", self.id, "symbol:", self.info.name, "sketch:", self.sketch, "extra root:", self.is_extra_root)
        for symbol, subtrees in self.subtree_list.items():
            print(symbol, ":", " ".join(list(map(lambda x: str(x.id), subtrees))))
        for symbol, subtrees in self.subtree_list.items():
            for subtree in subtrees:
                subtree.print_tree()

    def node_get_structure_constraint(self, soft_list, hard_list):
        assert not self.is_death
        if self.sketch:
            if self.has_special:
                soft_list.append(self.used_var)
            else:
                hard_list.append(self.used_var)
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
                        if operator[0] == "=" and operator[1] == "StartBool": continue
                        if self.has_special:
                            hard_list.append(self.operator_indicators[i])
                        else:
                            soft_list.append(self.operator_indicators[i])

            else:
                for (i, terminal) in enumerate(self.terminals):
                    if terminal == self.sketch:
                        if self.has_special:
                            hard_list.append(self.terminal_indicators[i])
                        else:
                            soft_list.append(self.terminal_indicators[i])
        for (i, operator) in enumerate(self.operators):
            #print(operator)
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
        if not self.is_extra_root:
            hard_list.append(z3.Implies(z3.Not(self.used_var), z3.And(all_used)))
        for symbol, subtrees in self.subtree_list.items():
            for subtree in subtrees:
                subtree.node_get_structure_constraint(soft_list, hard_list)

    def node_get_io_constraint(self, input, hard_list):
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
                subtree_result[symbol].append(subtree.node_get_io_constraint(input, hard_list))
        for (i, operator) in enumerate(self.operators):
            subexpr_values = []
            symbol_count = {}
            for subexpr in operator[1:]:
                if subexpr not in symbol_count: symbol_count[subexpr] = 0
                subexpr_values.append(subtree_result[subexpr][symbol_count[subexpr]])
                symbol_count[subexpr] += 1
            hard_list.append(z3.Implies(self.operator_indicators[i],
                                        return_value == operators.string2z3[operator[0]](subexpr_values)))
        if self.is_extra_root:
            hard_list.append(z3.Implies(z3.Not(self.used_var),
                                        return_value == subtree_result[self.symbol][0]))
        self.result_var = return_value
        return return_value

    def node_parse_output(self, model):
        if self.is_extra_root and z3.is_false(model[self.used_var]):
            #print("godown")
            return self.fixed_child.node_parse_output(model)
        assert z3.is_true(model[self.used_var])
        for (i, terminal) in enumerate(self.terminals):
            if z3.is_true(model[self.terminal_indicators[i]]):
            #    print("terminal")
                return terminal
        for (i, operator) in enumerate(self.operators):
            if z3.is_true(model[self.operator_indicators[i]]):
                subexpr_count = {}
                result = [operator[0]]
                for subexpr in operator[1:]:
                    if subexpr not in subexpr_count:
                        subexpr_count[subexpr] = 0
                    result.append(self.subtree_list[subexpr][subexpr_count[subexpr]].node_parse_output(model))
                    subexpr_count[subexpr] += 1
                '''if self.result_var is not None:
                    result_var = [operator[0], model[self.result_var]]
                    subexpr_count = {}
                    for subexpr in operator[1:]:
                        if subexpr not in subexpr_count:
                            subexpr_count[subexpr] = 0
                        result_var.append(model[self.subtree_list[subexpr][subexpr_count[subexpr]].result_var])
                        subexpr_count[subexpr] += 1
                    print(result_var)'''

                return result
        assert False

class FunctionTree:

    def __init__(self, function):
        start_symbol = "Start"
        for name, info in function.none_term.items():
            if info.type == function.return_type:
                start_symbol = name
        #print(function.sketch)
        self.root = Node(start_symbol, function.sketch, -config.depth, function, True)
        #self.root.print_tree()
        self.possible_root = []
        self.function = function
        now = self.root
        self.possible_root.append(now)
        while now.is_extra_root:
            now = now.fixed_child
            self.possible_root.append(now)
        #print("current", function.name)
        #self.root.print_tree()

    def get_structure_constraint(self, hard_cons_list, soft_cons_list):
        self.root.node_get_structure_constraint(soft_cons_list, hard_cons_list)
        root_used_var = list(map(lambda x: x.used_var, self.possible_root))
        hard_cons_list.append(root_used_var[-1])
        for i in range(len(root_used_var)-1):
            hard_cons_list.append(z3.Implies(root_used_var[i], root_used_var[i+1]))

    def get_o(self, input, hard_cons_list):
        return self.root.node_get_io_constraint(input, hard_cons_list)

    def get_io_constraint(self, input, output, hard_cons_list):
        hard_cons_list.append(self.get_o(input, hard_cons_list) == output)

    def _check_inp_variable_used(self, expression, name):
        if type(expression) == str:
            return expression == name
        if type(expression) == tuple:
            return False
        if type(expression) == list:
            for subexpr in expression[1:]:
                if self._check_inp_variable_used(subexpr, name):
                    return True
            return False
        assert False

    def get_heuristic_constraint(self, hard_list, soft_list):
        arg_list = self.function.arg_list
        symbolic_input1 = get_new_symbolic_input(arg_list)
        symbolic_input2 = get_new_symbolic_input(arg_list)
        hard_list.append(self.get_o(symbolic_input1, hard_list) !=
                         self.get_o(symbolic_input2, hard_list))

        for arg_info in arg_list:
            symbolic_input1 = get_new_symbolic_input(arg_list)
            symbolic_input2 = {}
            for name, var in symbolic_input1.items():
                symbolic_input2[name] = var
                if name == arg_info.name:
                    symbolic_input2[name] = new_variable(arg_info.type)
            #print("addsymbolic")
            #print(symbolic_input1)
            #print(symbolic_input2)
            if self._check_inp_variable_used(self.function.sketch, arg_info.name):
                soft_list.append(self.get_o(symbolic_input1, hard_list) !=
                                 self.get_o(symbolic_input2, hard_list))

    def parse_output(self, model):
        return self.root.node_parse_output(model)