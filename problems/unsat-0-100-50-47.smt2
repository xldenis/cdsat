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
(assert (= (and true x9) x2))
(assert (or (or (and x13 (= false (and false false))) (or x14 x13)) (or (or (or true false) x13) (= (and true false) (or false (and false false))))))
(assert (or (and false true) false))
(assert (= (= false (= true x7)) (or (or x19 false) (and x12 x29))))
(assert (and (and x18 false) (and (= x12 x25) (and true x13))))
(assert (and false x2))
(assert (and (or true false) true))
(assert (= (= false x27) (= (= x7 true) (or x14 x8))))
(assert (and x26 false))
(assert (and true (= x8 (= (= x14 x25) (or false false)))))
(check-sat)
