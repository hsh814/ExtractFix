(set-logic LIA)

(synth-fun f ((x1 Int) (x0 Int) (x2 Int)) Int
    ((Start Int (x0
                 x1
                 x2
                 2
                 3
                 (+ Start Start)
                 (- Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<  Start Start)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var x2 Int)

(constraint (not (and (>= (f x0 x1 x2) 0) (<= (- x2 x0)  (+ x1 3) ))))

(check-synth)

(sketch (- (- (- x2 x0) x1) 3))
