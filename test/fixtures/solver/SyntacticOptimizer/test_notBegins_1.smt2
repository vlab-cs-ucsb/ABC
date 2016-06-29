(set-logic QF_S)

(declare-fun a () String)

(assert (not (begins (concat "b" a) "a" )))

(check-sat)
