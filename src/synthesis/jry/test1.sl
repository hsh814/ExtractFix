(set-logic LIA)

(synth-fun f ((x Int)) Int
    ((Start Int (x
                 1
                 2
                 (+ Start Start)))))

(synth-fun g ((x Int)) Int
    ((Start Int (x
                 1
                 2
                 (+ Start Start)))))

(declare-var x Int)

(constraint (or (> x 3) (< (g (+ (f x) 1)) 7)))

(check-synth)

(sketch f (+ x 1))
(sketch g (+ x 2))
