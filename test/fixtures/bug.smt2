(set-logic QF_S)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (= (+ x (* 2 y) (* 3 z) 7) 0))

(check-sat)