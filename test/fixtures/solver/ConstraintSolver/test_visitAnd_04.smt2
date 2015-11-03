(set-logic QF_S)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (> (+ (* 2 x) (* 3 y)) 5))
(assert (<= (- x 3) (* 2 y)))

(check-sat)

