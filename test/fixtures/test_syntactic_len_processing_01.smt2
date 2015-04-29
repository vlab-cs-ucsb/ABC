(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (len abc) 0))
(assert (= 5 (len abc)))
(assert (> (len abc) 6))
(assert (> 6 (len abc)))
(assert (>= (len abc) 7))
(assert (>= 7 (len abc)))
(assert (< (len abc) 8))
(assert (< 8 (len abc)))
(assert (<= (len abc) 9))
(assert (<= 9 (len abc)))

(check-sat)

