(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (indexOf var_abc "b") 2))

(check-sat)

