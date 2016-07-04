(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)


(assert (contains b (concat a "vlab")))

(check-sat)

