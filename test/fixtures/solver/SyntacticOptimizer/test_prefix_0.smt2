(set-logic QF_S)

(declare-fun a () String)

(assert (= (concat "b" a) "a"))

(check-sat)
