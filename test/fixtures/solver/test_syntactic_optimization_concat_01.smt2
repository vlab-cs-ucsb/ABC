(set-logic QF_S)

(declare-fun var_abc () String)
(declare-fun var_bak () String)

(assert (= var_abc (concat "b" "a" "k" "i")))
(assert (= var_abc (concat "b" (concat (concat "a" "k") (concat "i" "a" "y")))))
(assert (= var_abc (concat var_bak (concat (concat var_bak var_bak "b" "a") (concat "k" "i" var_bak)))))
(assert (= var_abc (concat var_bak (concat (concat var_bak "b" "a") (concat "k" "i" var_bak "a" "y") (concat "d" "i" (concat "n" var_bak))))))
(check-sat)

