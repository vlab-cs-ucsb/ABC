(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)



(assert (= (concat "a" b) c))

(check-sat)

