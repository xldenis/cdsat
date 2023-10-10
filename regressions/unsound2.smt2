(declare-const r0 Real)
(declare-const r1 Real)
(declare-const r2 Real)

(assert (= 3 r1))
(assert (= r0 r1))

(check-sat)


