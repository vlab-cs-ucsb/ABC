(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (indexOf var_abc "baki") (len /(12|1234567)/) ))

(check-sat)

