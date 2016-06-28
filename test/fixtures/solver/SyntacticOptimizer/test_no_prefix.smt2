(set-logic QF_S)

(declare-fun a () String)

(assert (= (concat a "b") "a"))

(check-sat)

