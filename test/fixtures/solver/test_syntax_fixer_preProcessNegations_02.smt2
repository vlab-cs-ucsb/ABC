(set-logic QF_S)
(declare-fun abc () String)

(assert (not (or (= abc "abc") (= abc "cba") (= abc "vlab"))))

(check-sat)

