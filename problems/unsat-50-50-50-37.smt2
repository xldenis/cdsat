(declare-const x0 Bool)
(declare-const x1 Bool)
(declare-const x2 Bool)
(declare-const x3 Bool)
(declare-const x4 Bool)
(declare-const x5 Bool)
(declare-const x6 Bool)
(declare-const x7 Bool)
(declare-const x8 Bool)
(declare-const x9 Bool)
(declare-const x10 Bool)
(declare-const x11 Bool)
(declare-const x12 Bool)
(declare-const x13 Bool)
(declare-const x14 Bool)
(declare-const x15 Bool)
(declare-const x16 Bool)
(declare-const x17 Bool)
(declare-const x18 Bool)
(declare-const x19 Bool)
(declare-const x20 Bool)
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
(assert (and (and x0 x4) (and x6 (= y6 y7))))
(assert (= (and (or false false) x16) x17))
(assert (< (+ 3 (+ y1 y3)) 81))
(assert (= x6 (= false true)))
(assert (= y8 22))
(assert x14)
(assert (and x3 (or x5 x9)))
(assert (or (= y4 55) (and true true)))
(assert (< y7 75))
(assert (or false false))
(check-sat)
