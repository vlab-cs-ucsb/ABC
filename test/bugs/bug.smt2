(set-logic QF_S)
(declare-fun abc () String)
(assert (not (= abc "abc")))
(check-sat abc)