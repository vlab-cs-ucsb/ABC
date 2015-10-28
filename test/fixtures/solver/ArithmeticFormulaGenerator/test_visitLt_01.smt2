(set-logic QF_S)

(declare-fun x () Int)

(assert (< x 3))

(check-sat)
