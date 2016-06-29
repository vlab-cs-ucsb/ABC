(set-logic QF_S)

(declare-fun a () String)

(assert (begins (concat "a" a) "a" ))

(check-sat)

