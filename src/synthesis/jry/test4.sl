(set-logic LIA)

(synth-fun f ((s Int) (spp Int)) Bool
    ((Start Int (s
                 spp
                 8
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
(declare-var s Int)
(declare-var spp Int)

(constraint (=> (= (f s spp) false) (and (< s spp) (< s 8))))

(check-synth)

(sketch f (< s spp))