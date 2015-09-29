(set-logic QF_S)
(declare-fun abc () String)

(assert (not (and (= abc "abc") (= abc "cba") (= abc "vlab"))))

(check-sat)

