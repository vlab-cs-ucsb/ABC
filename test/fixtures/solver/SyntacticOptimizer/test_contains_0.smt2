(set-logic QF_S)

(declare-fun a () String)

(assert (contains (concat "a" a) "a" ))

(check-sat)

