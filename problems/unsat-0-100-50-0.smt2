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
(assert (or x3 x0))
(assert (and true (= x6 true)))
(assert (or false x7))
(assert x12)
(assert (or (= false (or (= x4 x4) (= true x12))) (and x3 x4)))
(assert (= (and (= true x14) (and (or true false) false)) (= true x6)))
(assert (and x14 (and x2 false)))
(assert (and (and (= x6 true) true) (= true x6)))
(assert (= (or false false) (and x10 true)))
(assert (= (or (or x3 false) x16) (and x0 x11)))
(check-sat)
