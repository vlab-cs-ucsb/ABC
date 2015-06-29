(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (len var_abc) 0))
(assert (= 5 (len var_abc)))
(assert (> (len var_abc) 6))
(assert (> 6 (len var_abc)))
(assert (>= (len var_abc) 7))
(assert (>= 7 (len var_abc)))
(assert (< (len var_abc) 8))
(assert (< 8 (len var_abc)))
(assert (<= (len var_abc) 9))
(assert (<= 9 (len var_abc)))

(check-sat)

