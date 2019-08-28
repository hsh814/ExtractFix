import sys

#sys.path.append(os.path.dirname(os.path.realpath(__file__)))
sys.path.append("/Users/pro/Desktop/work/2019S/z3/build/python")

from parser import task
from synthesis.buildtree import FunctionTree
from synthesis import solver
from filter import trivial, correctside, condition
from translator import trans
from util import operators
import config
import os

if __name__ == "__main__":
    sys.argv = [None,
                "A.txt",
                "B.txt"]
    log_path = "."
    config.is_overflow = False
    #if config.is_overflow:
    #    operators.use_signed_operator()
    sketches = trans.trans(sys.argv[1], sys.argv[2])
    synthesis_task = task.SynthesisTask("mid.sl")
    #import pprint as pp
    #pp.pprint(synthesis_task.constraint)
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
        if len(sketches) == 1 and len(synthesis_task.function_list) == 1 and \
                        "condition1" in synthesis_task.function_list:
            #import pprint as pp
            #pp.pprint(synthesis_task.constraint)
            candidates = [{"condition1": synthesis_task.constraint[0][2]}]
        else:
            candidates = synthesizer.solve(synthesis_task, False)
    assert len(candidates) > 0
    #result = condition.filter(candidates, synthesis_task)
    #if result is None:
    result = trivial.filter(candidates, synthesis_task)

    for sketch in sketches:
        sketch["patch"] = None
        for name, res in result.items():
            if name == sketch["func"].expr:
                sketch["patch"] = sketch["left_sketch"] + trans.trans_to_cpp(res) + sketch["right_sketch"]
    print("generated patch is: ")
    patch_file = os.path.join(log_path, "patch")
    with open(patch_file, "w+") as f:
        for sketch in sketches:
            print(sketch["patch"])
            f.write(sketch["patch"])
'''
    assert len(result) == 1
    patch = None
    for name, res in result.items():
        patch = trans.trans_to_cpp(res)
    well_formed_patch = left_sketch + patch + right_sketch
    print("generated patch is: ", well_formed_patch)

    patch_file = os.path.join(log_path, "patch")
    with open(patch_file, 'w+') as f:
        f.write(well_formed_patch)'''

