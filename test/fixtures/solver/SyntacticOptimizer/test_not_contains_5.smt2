(set-logic QF_S)

(declare-fun a () String)

(assert (not (contains (concat (concat "a" a) "b") "ab" )))

(check-sat)

