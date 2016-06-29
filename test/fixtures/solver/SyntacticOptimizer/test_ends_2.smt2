(set-logic QF_S)

(declare-fun a () String)

(assert (ends (concat a "bbb") "b" ))

(check-sat)

