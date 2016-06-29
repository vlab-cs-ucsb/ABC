(set-logic QF_S)

(declare-fun a () String)

(assert (not (ends (concat a "aba") "abc" )))

(check-sat)

