(set-logic QF_S)

(declare-fun a () String)

(assert (= "b" "a"))

(check-sat)

