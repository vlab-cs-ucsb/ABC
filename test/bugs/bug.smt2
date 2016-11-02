(set-logic QF_S)
(declare-fun s () String)
(assert (not (= s "ab")))
(check-sat s)