(set-logic QF_S)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (< y x))

(check-sat)
