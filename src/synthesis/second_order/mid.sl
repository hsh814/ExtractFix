(synth-fun len ((prevalue__len Int)) Int ((Start Int (-1 0 1 -3 -2 2 (+ Start Start) prevalue__len)) (StartBool Bool ((< Start Start) (<= Start Start) (and StartBool StartBool) (or StartBool StartBool) (not StartBool) (= Start Start) (= StartBool StartBool)))))
(declare-var prevalue__len Int)
(constraint (<= 0 (+ -2 (len prevalue__len))))
(sketch len (+ 1 prevalue__len))