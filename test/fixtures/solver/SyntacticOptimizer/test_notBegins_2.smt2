(set-logic QF_S)

(declare-fun a () String)

(assert (not (begins (concat "bbb" a) "b" )))

(check-sat)

