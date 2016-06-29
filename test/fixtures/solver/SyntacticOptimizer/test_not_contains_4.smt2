(set-logic QF_S)

(declare-fun a () String)

(assert (not (contains "a" "b" )))

(check-sat)

