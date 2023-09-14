(declare-const x Real)
(declare-const a Bool)
(declare-const b Bool)

(assert (< x 10))
(assert (and a b))
(assert (or (not b) (not (or (= x 15) (< x 15)))))

