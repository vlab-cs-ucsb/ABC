(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)



(assert (= (concat b "a") c))

(check-sat)

