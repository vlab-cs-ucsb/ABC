(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (charAt "abc" 1)))

(check-sat)

