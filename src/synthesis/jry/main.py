import sys
sys.path.append("/Users/pro/Desktop/work/2019S/z3/build/python")
from parser import task
from synthesis.buildtree import FunctionTree
from synthesis.solver import synthesis
from util import common

if __name__ == "__main__":
    sys.argv = [None, "test4.sl"]
    file_name = sys.argv[1]
    synthesis_task = task.SynthesisTask(file_name)
    function_tree_list = {}
    for function_name, function_info in synthesis_task.function_list.items():
        function_tree = FunctionTree(function_info)
        function_tree_list[function_name] = function_tree
    synthesis_task.set_function_tree(function_tree_list)
    result = synthesis(synthesis_task)
    assert result == 0
    for function_name, function_result in synthesis_task.result.items():
        common.print_function(function_result, synthesis_task.function_list[function_name])