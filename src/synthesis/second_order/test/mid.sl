(synth-fun condition ((i Int) (size Int)) Bool ((Start Int (1 2 3 95109119 95109120 95109121 (+ Start Start) (- Start Start) (div Start Constant) i size)) (StartBool Bool (true false (< Start Start) (<= Start Start) (and StartBool StartBool) (or StartBool StartBool) (not StartBool) (= Start Start) (= StartBool StartBool))) (Constant Int (1 2 3 95109119 95109120 95109121))))
(declare-var i Int)
(declare-var size Int)
(constraint (=> (not (condition i size)) (or (not (and (= False (< i (div size 2))) (< i size))) (<= (+ 95109120 (- size i)) (+ 95109120 i)))))
(sketch condition (< i (div size 2)))