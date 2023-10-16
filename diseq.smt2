(declare-const r0 Real)

(assert (= (= r0 1) false))
(assert (<= r0 1))
(assert (>= r0 1))

(check-sat)