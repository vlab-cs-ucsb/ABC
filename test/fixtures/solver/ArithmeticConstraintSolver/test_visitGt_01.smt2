(set-logic QF_S)

(declare-fun x () Int)

(assert (> x 0))

(check-sat)

