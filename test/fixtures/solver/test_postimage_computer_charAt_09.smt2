(set-logic QF_S)

(declare-fun var_abc () String)

(assert (=  (charAt var_abc 2) "k"))

(check-sat)

