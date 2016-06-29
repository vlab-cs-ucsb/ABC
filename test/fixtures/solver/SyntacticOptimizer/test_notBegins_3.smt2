(set-logic QF_S)

(declare-fun a () String)

(assert (not (begins (concat "aba" a) "abc" )))

(check-sat)

