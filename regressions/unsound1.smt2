(declare-const r0 Real)
(declare-const r1 Real)
(declare-const r2 Real)

(assert (= (+ 88 2) (+ 35 r2)))
(assert (= (< r2 44) (< r0 r1)))
(check-sat)
