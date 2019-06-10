(set-logic LIA)

(synth-fun cond ((x0 Int) (x1 Int) (x2 Int)) Int
    ((Start Int (x0
                 x1
                 x2
                 4
                 (+ Start Start)
                 (- Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var x2 Int)

(constraint (not (and (> (cond x0 x1 x2) 0) (>= (- (+ x0 x1) 3) x2))))

(check-synth)

