(set-logic QF_S)

(declare-fun a () String)

(assert (contains "a" "a" ))

(check-sat)

