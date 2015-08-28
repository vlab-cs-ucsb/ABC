(set-logic QF_S)

(declare-fun var_abc () String)
(declare-fun tmp () String)

(assert (= tmp "abc"))
(assert (= var_abc (replace tmp "b" "z")))

(check-sat)

