(set-logic QF_S)

(declare-fun x () String)

(assert (not (in x "/(01)*/")))
(assert (>= (len x) 1))

(check-sat)

