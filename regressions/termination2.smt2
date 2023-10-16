(declare-const r0 Real)
(declare-const r1 Real)

(assert (= (= r1 1) (= 0 r0)))
(assert (= 0 r1))
(check-sat)
