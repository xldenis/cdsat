(declare-const y0 Real)
(declare-const y1 Real)
(declare-const y2 Real)
(declare-const y3 Real)
(declare-const y4 Real)
(declare-const y5 Real)
(declare-const y6 Real)
(declare-const y7 Real)
(declare-const y8 Real)
(declare-const y9 Real)
(declare-const y10 Real)
(assert (= 47 y1))
(assert true)
(assert (< 76 (+ 58 31)))
(assert (= (= false false) (= true (< y5 75))))
(assert (= y8 y9))
(assert (< y3 78))
(assert (< 81 y4))
(assert (= (= (< y4 y7) (= y8 y10)) (= false (< y1 38))))
(assert (< (+ y8 12) y4))
(assert true)
(check-sat)
