(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (charAt /ab+c/ 3)))

(check-sat)