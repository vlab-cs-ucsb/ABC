(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (indexOf var_abc "baki") 2))

(check-sat)

