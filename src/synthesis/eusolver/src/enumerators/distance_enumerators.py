from utils import utils
from exprs import evaluation
from utils import basetypes
from exprs import exprs
from exprs import exprtypes
from sketch import distance
from sketch import config
import copy
import queue

class ExtendUnit:
    def __init__(self, distance, expression):
        self.distance = distance
        self.expression = expression

    def __lt__(self, other):
        return self.distance < other.distance

class DistanceBasedEnumerator():

    def __init__(self, grammars, sketch, sketch_expression):
        self.grammars = grammars
        self.sketch = sketch
        self.sketch_expression = sketch_expression

        '''rules = grammars.rules
        for symbol, extensions in rules.items():
            print(symbol, ":")
            for extension in extensions:
                template_expression = extension.to_template_expr()
                print(exprs.expression_to_string(template_expression[2]))
                import pprint as pp
                pp.pprint(template_expression[2])'''

    # do not use
    def set_size(self, size):
        return 0

    def _check_match(self, expression, extension):
        extend_expression = extension.to_template_expr()[2]
        return exprs.soft_equals(extend_expression, expression)

    def _subGenerator(self, expression):
        if exprs.is_constant_expression(expression) or exprs.is_formal_parameter_expression(expression):
            for symbol, extensions in self.grammars.rules.items():
                if symbol == "ConstantIntegerType":
                    continue
                for extension in extensions:
                    if self._check_match(expression, extension):
                        yield exprs.VariableExpression(
                            exprs.VariableInfo(self.grammars.nt_type[symbol], symbol))
        elif exprs.is_variable_expression(expression):
            for symbol, extensions in self.grammars.rules.items():
                if symbol == exprs.normalize_variable_name(expression.variable_info.variable_name):
                    for extension in extensions:
                        yield extension.to_template_expr()[2]
        else:
            for (pos, subexpr) in enumerate(expression.children):
                gen = self._subGenerator(subexpr)
                try:
                    while True:
                        childrenList = [expr for expr in expression.children]
                        childrenList[pos] = next(gen)
                        yield exprs.FunctionExpression(expression.function_info, tuple(childrenList))
                except StopIteration:
                    continue
            for symbol, extensions in self.grammars.rules.items():
                if symbol == "ConstantIntegerType":
                    continue
                for extension in extensions:
                    if self._check_match(expression, extension):
                        yield exprs.VariableExpression(
                            exprs.VariableInfo(self.grammars.nt_type[symbol], symbol))

    def _get_cost(self, expression):
        return len(exprs.get_all_variables(expression))

    def generate(self):
        Q = queue.PriorityQueue()
        Q.put_nowait(ExtendUnit(0, self.sketch_expression))
        dic = {self.sketch_expression}
        while Q.not_empty:
            current_unit = Q.get_nowait()
            expression = current_unit.expression
            distance = current_unit.distance - self._get_cost(expression)
            generator = self._subGenerator(expression)
            #print("Deal with")
            #print(exprs.expression_to_string(expression))
            try:
                while True:
                    next_expression = next(generator)
                    str_expr = exprs.expression_to_string(next_expression)
                    #print("result ", str_expr)
                    if str_expr not in dic:
                        dic.add(str_expr)
                        next_distance = self._get_cost(next_expression)
                        Q.put_nowait(ExtendUnit(next_distance + distance, next_expression))
                        if next_distance == 0:
                            yield next_expression
            except StopIteration:
                continue
        #print("Fail")

