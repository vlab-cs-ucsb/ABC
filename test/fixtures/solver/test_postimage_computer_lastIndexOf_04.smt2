(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (lastIndexOf var_abc "b") (len /(12|1234567)/) ))

(check-sat)

