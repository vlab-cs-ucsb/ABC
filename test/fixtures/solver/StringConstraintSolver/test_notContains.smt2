(set-logic QF_S)

(declare-fun a0 () String)
(declare-fun a1 () String)
(declare-fun a2 () String)

(assert
(and

(not (contains a0 a1))
(= a0 a1)

))
(check-sat)

