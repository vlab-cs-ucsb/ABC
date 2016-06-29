(set-logic QF_S)

(declare-fun a () String)

(assert (contains (concat (concat "a" a) "b") "ab" ))

(check-sat)

