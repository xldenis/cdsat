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
(declare-const y0 Real)
(assert (= 42 66))
(assert (= (and x10 (= y0 y0)) (< 23 y0)))
(assert (and (< 83 y0) (< y0 y0)))
(assert (< y0 17))
(assert (or true true))
(assert (and x10 false))
(assert (= 22 (+ y0 y0)))
(assert (and (= (+ y0 y0) y0) x9))
(assert (or (or x9 x17) (< y0 y0)))
(assert (< y0 y0))
(check-sat)
