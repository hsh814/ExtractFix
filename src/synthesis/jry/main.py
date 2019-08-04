import sys
sys.path.append("/Users/pro/Desktop/work/2019S/z3/build/python")
from parser import task
from synthesis.buildtree import FunctionTree
from synthesis import solver
from filter import trivial, correctside, condition
from translator import trans
from util import common

if __name__ == "__main__":
    sys.argv = [None,
                "../../../benchmark/libtiff-10094/result1/constraints.txt",
                "../../../benchmark/libtiff-10094/result1/fix_stm.txt"]
    left_sketch, right_sketch = trans.trans(sys.argv[1], sys.argv[2])
    synthesis_task = task.SynthesisTask("mid.sl")
    function_tree_list = {}
    for function_name, function_info in synthesis_task.function_list.items():
        function_tree = FunctionTree(function_info)
        function_tree_list[function_name] = function_tree
    synthesis_task.set_function_tree(function_tree_list)
    synthesizer = solver.SyntaxSolver()
    candidates = synthesizer.solve(synthesis_task, True)
    #print("finish ", len(candidates))
    if len(candidates) == 0:
        #print(left_sketch, synthesis_task.function_list)
        if left_sketch.strip()[-1] != "=" and len(synthesis_task.function_list) == 1 and \
                        "condition" in synthesis_task.function_list:
            #import pprint as pp
            #pp.pprint(synthesis_task.constraint)
            candidates = [{"condition": synthesis_task.constraint[0][2]}]
        else:
            candidates = synthesizer.solve(synthesis_task, False)
    assert len(candidates) > 0
    result = condition.filter(candidates, synthesis_task)
    if result is None:
        result = trivial.filter(candidates, synthesis_task)
    #TODO: support multiline fix
    assert len(result) == 1
    patch = None
    for name, res in result.items():
        patch = trans.trans_to_cpp(res)
    print(left_sketch + patch + right_sketch)
