(set-logic QF_S)

(declare-fun a () String)

(assert (ends (concat a "a") "a" ))

(check-sat)

