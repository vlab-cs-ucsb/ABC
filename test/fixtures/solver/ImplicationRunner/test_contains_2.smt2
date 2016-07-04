(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)


(assert (contains (concat a "vlab") b))

(check-sat)

