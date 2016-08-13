(set-logic QF_S)

(declare-fun a0 () String)
(declare-fun a1 () String)

(assert
(and

(!= a0 a1)

))
(check-sat)

