(set-logic QF_S)
(declare-fun abc () String)

(assert (not (not (not ( not (not (= abc "vlab")))))))
(assert (not (not (not ( not (= abc "ucsb"))))))

(check-sat)

