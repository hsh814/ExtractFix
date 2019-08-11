(set-logic LIA)

(synth-fun cond ((a0 Int) (a1 Int)) Int
    ((Start Int (a0
                 a1
                 (+ Start Start)
                 (- Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))
(declare-var x0 Int)
(declare-var x1 Int)

(constraint (=> (and (>= x0 1) (>= x1 2)) (>= (cond x0 x1) 3)))

(check-synth)

(sketch cond (- a0 a1))
