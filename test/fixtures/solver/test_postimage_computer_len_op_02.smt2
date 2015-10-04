(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (len var_abc) 3))

(check-sat)

