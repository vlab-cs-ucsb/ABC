(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (lastIndexOf /(ucsb|abc)abcvlab/ "abc")))

(check-sat)

