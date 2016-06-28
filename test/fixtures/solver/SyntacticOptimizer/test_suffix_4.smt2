(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)


(assert (= (concat a "b") (concat b "a")))

(check-sat)
