(set-logic QF_S)
(declare-fun abc () String)

(assert (not (= "an" "an")))
	

(check-sat)

