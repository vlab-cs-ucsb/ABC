(set-logic QF_S)

(declare-fun a () String)

(assert (not (contains (concat "a" a) "a" )))

(check-sat)

