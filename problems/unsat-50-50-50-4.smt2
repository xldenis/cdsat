(declare-const x0 Bool)
(declare-const x1 Bool)
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
(declare-const y11 Real)
(declare-const y12 Real)
(declare-const y13 Real)
(declare-const y14 Real)
(declare-const y15 Real)
(declare-const y16 Real)
(declare-const y17 Real)
(declare-const y18 Real)
(declare-const y19 Real)
(declare-const y20 Real)
(declare-const y21 Real)
(declare-const y22 Real)
(declare-const y23 Real)
(declare-const y24 Real)
(declare-const y25 Real)
(declare-const y26 Real)
(assert (and (< (+ y24 25) y1) (or x1 (and false (= y24 y2)))))
(assert (= y26 (+ 7 (+ y13 33))))
(assert (= x1 true))
(assert (or true false))
(assert (= (= x0 (< 38 y1)) (< 47 71)))
(assert (or (< 9 7) (= (and x0 false) (< 43 y18))))
(assert (= true (and false true)))
(assert (= (= (+ y16 y9) y10) (< 33 y15)))
(assert (< 13 13))
(check-sat)
