(set-logic QF_S)

(declare-fun a () String)

(assert (= (concat "aa" a) "a"))

(check-sat)
