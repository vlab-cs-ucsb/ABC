(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)


(assert (= (concat "a" (concat a "b" )) (concat "a" (concat b "b"))))

(check-sat)
