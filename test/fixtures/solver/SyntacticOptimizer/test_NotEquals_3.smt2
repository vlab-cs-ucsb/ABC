(set-logic QF_S)
(declare-fun a () String)
(declare-fun b () String)


(assert (not (= "abc" "abd")))
	

(check-sat)