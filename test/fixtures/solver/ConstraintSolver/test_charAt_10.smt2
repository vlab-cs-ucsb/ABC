(set-logic QF_S)

(declare-fun var_abc () String)

(assert (=  (charAt var_abc 0) "b"))
(assert (=  (charAt var_abc 1) "a"))
(assert (=  (charAt var_abc 2) "k"))
(assert (=  (charAt var_abc 3) "i"))
(assert (=  (charAt var_abc 4) /(a|y|d|i|n)/))

(check-sat)

