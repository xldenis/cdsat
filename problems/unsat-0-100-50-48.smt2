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
(declare-const x21 Bool)
(declare-const x22 Bool)
(declare-const x23 Bool)
(declare-const x24 Bool)
(declare-const x25 Bool)
(declare-const x26 Bool)
(declare-const x27 Bool)
(declare-const x28 Bool)
(declare-const x29 Bool)
(declare-const x30 Bool)
(declare-const x31 Bool)
(declare-const x32 Bool)
(declare-const x33 Bool)
(declare-const x34 Bool)
(assert true)
(assert (and (and true true) x32))
(assert (and false (and (or (or false true) false) (and false x21))))
(assert (= false (or x18 true)))
(assert (= true (and x23 x10)))
(assert (and (= false x12) (and true x27)))
(assert (= x3 true))
(assert (and true (and false x21)))
(assert (or false (or false x2)))
(assert (and (and x0 (= x4 false)) (or x29 x16)))
(check-sat)
