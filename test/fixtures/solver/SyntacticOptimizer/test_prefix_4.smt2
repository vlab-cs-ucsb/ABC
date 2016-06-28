(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)


(assert (= (concat "b" a) (concat "a" b)))

(check-sat)
