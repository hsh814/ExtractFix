from parser import sexp
import pprint as pp
import z3

class NoneTerm:
    def __init__(self, declare_list):
        self.rules = declare_list[2]
        self.name = declare_list[0]
        self.type = declare_list[1]
        #print("NoneTerm", self.type, self.name)

class Variable:
    def __init__(self, name, var_type, change_name=False):
        self.name = name
        if change_name:
            name = "inputvar" + name
        self.type = var_type
        self.z3_var = None
        if self.type == "Bool":
            self.z3_var = z3.Bool(name)
        elif self.type == "Int":
            self.z3_var = z3.Int(name)
        else:
            assert False

class Function:
    def __init__(self, declare_list):
        self.return_type = declare_list[3]
        self.arg_table = {}
        self.none_term = {}
        self.arg_list = []
        self.name = declare_list[1]
        for name, arg_type in declare_list[2]:
            self.arg_table[name] = Variable(name, arg_type)
            self.arg_list.append(self.arg_table[name])
        for none_term_info in declare_list[4]:
            self.none_term[none_term_info[0]] = NoneTerm(none_term_info)
        self.sketch = None

    def set_sketch(self, sketch):
        self.sketch = sketch

class SynthesisTask:
    def _strip_comments(self, bmFile):
        noComments = '('
        for line in bmFile:
            line = line.split(';', 1)[0]
            noComments += line
        return noComments + ')'

    def __init__(self, file_name):
        input_file = open(file_name, "r")
        bm = self._strip_comments(input_file)
        self.bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
        self.function_list = {}
        self.variable_list = {}
        self.constraint = []
        self.function_tree_list = None
        self.result = None

        #pp.pprint(self.bmExpr)
        for expr in self.bmExpr:
            expr_type = expr[0]
            #print(expr_type)
            if expr_type == "set-logic":
                assert expr[1] == "LIA"
            elif expr_type == "synth-fun":
                function_name = expr[1]
                self.function_list[function_name] = Function(expr)
            elif expr_type == "declare-var":
                name = expr[1]
                variable_type = expr[2]
                self.variable_list[name] = Variable(name, variable_type, True)
            elif expr_type == "constraint":
                self.constraint.append(expr[1])
            elif expr_type == "sketch":
                name = expr[1]
                self.function_list[name].set_sketch(expr[2])
            elif expr_type == "check-synth":
                continue
            else:
                assert False
        #print(self.constraint)

    def set_function_tree(self, function_tree_list):
        self.function_tree_list = function_tree_list

    def set_result(self, result):
        self.result = result
