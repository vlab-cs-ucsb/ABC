(set-logic QF_S)

(declare-fun a () String)

(assert (= (concat a "aa") "a"))

(check-sat)
