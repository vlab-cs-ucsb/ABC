(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)


(assert (= (concat "bbba" a) (concat "bbbba" b)))

(check-sat)
