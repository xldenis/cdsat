(declare-const y7 Real)
(declare-const y9 Real)
(declare-const y12 Real)
(declare-const y13 Real)
(declare-const y14 Real)
(declare-const y16 Real)
(declare-const y30 Real)
(declare-const y27 Real)
(declare-const y32 Real)
(declare-const y43 Real)
(declare-const y46 Real)
(declare-const y39 Real)
(declare-const y47 Real)
(declare-const y53 Real)

(assert (= (< y12 y14) (< y46 65)))
(assert (= (+ y47 85) y16))
(assert (= (+ 88 2) (+ 35 y53)))
(assert (< y53 75))
(check-sat)