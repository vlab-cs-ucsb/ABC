(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (subString /ab+c/ 3)))

(check-sat)