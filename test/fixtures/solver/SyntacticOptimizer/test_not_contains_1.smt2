(set-logic QF_S)

(declare-fun a () String)

(assert (not (contains (concat (concat "a" a) "a") "a" )))

(check-sat)

