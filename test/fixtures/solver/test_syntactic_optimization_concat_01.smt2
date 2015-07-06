(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (concat "b" (concat (concat "a" "k") (concat "i" "a" "y")))))

(check-sat)

