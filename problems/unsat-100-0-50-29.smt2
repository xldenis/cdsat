(declare-const y0 Real)
(declare-const y1 Real)
(declare-const y2 Real)
(declare-const y3 Real)
(declare-const y4 Real)
(declare-const y5 Real)
(declare-const y6 Real)
(declare-const y7 Real)
(assert (< 10 y3))
(assert (< y0 (+ y7 56)))
(assert (= (= (< 24 y0) true) (< y2 6)))
(assert (= y4 (+ 51 86)))
(assert (= (= (< 44 42) (< y3 y0)) (= true (< y0 y3))))
(assert (< 1 18))
(assert (< 34 y6))
(assert (< (+ 57 24) 34))
(check-sat)