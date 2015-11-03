(set-logic QF_S)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (= x (* 2 y)))

(check-sat)

