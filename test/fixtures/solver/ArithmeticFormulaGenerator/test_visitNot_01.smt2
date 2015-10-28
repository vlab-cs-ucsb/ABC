(set-logic QF_S)

(declare-fun var_abc () Int)

(assert (not (> var_abc 3)))

(check-sat)
