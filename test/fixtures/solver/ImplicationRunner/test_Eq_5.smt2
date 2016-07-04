(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)



(assert (= c (concat "a" b)))

(check-sat)

