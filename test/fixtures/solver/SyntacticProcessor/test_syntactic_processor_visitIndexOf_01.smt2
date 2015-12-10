(set-logic QF_S)
(declare-fun abc () String)

(assert (!=  (indexOf abc 122) (- 1)))

(check-sat)

