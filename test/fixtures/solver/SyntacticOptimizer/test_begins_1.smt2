(set-logic QF_S)

(declare-fun a () String)

(assert (begins (concat "b" a) "a" ))

(check-sat)

