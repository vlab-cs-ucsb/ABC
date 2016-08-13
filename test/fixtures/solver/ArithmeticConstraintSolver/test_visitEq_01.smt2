(set-logic QF_S)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (- 2) (* 2 y)))

(check-sat)

