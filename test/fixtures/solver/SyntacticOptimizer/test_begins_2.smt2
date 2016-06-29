(set-logic QF_S)

(declare-fun a () String)

(assert (begins (concat "bbb" a) "b" ))

(check-sat)

