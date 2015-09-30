(set-logic QF_S)
(declare-fun abc () String)

(assert (and (not (in abc "vlab.cs.ucsb")) (not (notIn abc /garbage/)) 
	(not (contains abc "cs")) (not (notContains abc /ece/)) (not (begins abc /vlab/)) (not (notBegins abc /ucsb/))
	(not (ends abc /ucsb/)) (not (notEnds abc /vlab/)) (not (not abc))))

(check-sat)

