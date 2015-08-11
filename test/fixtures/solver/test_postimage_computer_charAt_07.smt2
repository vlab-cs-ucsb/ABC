(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (charAt /ab*c/ 2)))

(check-sat)