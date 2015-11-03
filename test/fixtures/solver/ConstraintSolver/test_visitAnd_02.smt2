(set-logic QF_S)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (+ x y) 3))
(assert (= y 2))

(check-sat)

