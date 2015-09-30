(set-logic QF_S)
(declare-fun abc () String)

(assert (= abc "abc"))
(assert (= abc "cba"))

(check-sat)

