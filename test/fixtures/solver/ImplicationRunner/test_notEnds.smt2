(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)


(assert (not (ends b a)))

(check-sat)

