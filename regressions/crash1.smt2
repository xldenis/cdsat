(declare-const y2 Real)
(declare-const y7 Real)
(declare-const y11 Real)

(assert (= y11 44))
(assert (= (< y2 y7) (= y11 9)))

(check-sat)
