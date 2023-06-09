(set-logic LIA)

(synth-fun f ((x1 Int) (x0 Int) (x2 Int)) Int
    ((Start Int (x0
                 x1
                 x2
                 2
                 3
                 4
                 (+ Start Start)
                 (- Start Start)))
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

(sketch f (- (- (- x2 x0) x1) 3))