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
(declare-const x35 Bool)
(declare-const x36 Bool)
(declare-const x37 Bool)
(declare-const x38 Bool)
(declare-const x39 Bool)
(declare-const x40 Bool)
(declare-const x41 Bool)
(declare-const x42 Bool)
(declare-const x43 Bool)
(declare-const x44 Bool)
(declare-const x45 Bool)
(declare-const x46 Bool)
(declare-const x47 Bool)
(declare-const x48 Bool)
(declare-const x49 Bool)
(declare-const x50 Bool)
(declare-const x51 Bool)
(assert (= (and (or x25 x10) (and x0 true)) (or (or (and x51 false) (and (= x0 false) (and false x6))) (= (= x32 x28) (= x26 true)))))
(assert (or (and true x44) (and false true)))
(assert (= (= x7 true) true))
(assert (and (or true x27) (and (= false false) (= (or x2 (or false false)) false))))
(assert (= (and (or false x37) (= false (= x46 false))) (or (or x42 false) (and false false))))
(assert (and (or false (= x19 x8)) (and false x13)))
(assert (= (= x48 x14) (= (and x10 false) (= true x11))))
(assert (and (or false true) (and (or x41 false) (and false x49))))
(assert true)
(assert (or (= x49 (or (and x33 x15) (and (or true true) (= x34 true)))) x2))
(check-sat)