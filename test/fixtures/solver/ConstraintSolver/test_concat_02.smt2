(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (concat "b" "a" "ki")))

(check-sat)

