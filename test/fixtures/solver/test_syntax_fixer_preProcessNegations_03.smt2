(set-logic QF_S)
(declare-fun abc () String)

(assert (not (or (!= abc "xyz") (= abc "vlab.cs.ucsb") (and (in abc "vlab.cs.ucsb") (notIn abc /garbage/) 
	(contains abc "cs") (notContains abc /ece/) (begins abc /vlab/) (notBegins abc /ucsb/)
	(ends abc /ucsb/) (notEnds abc /vlab/)))))

(check-sat)

