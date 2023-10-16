(declare-const b0 Bool)
(declare-const r0 Real)
(assert (= 0 r0))
(assert (or  b0 (< r0 0)))
(check-sat)


