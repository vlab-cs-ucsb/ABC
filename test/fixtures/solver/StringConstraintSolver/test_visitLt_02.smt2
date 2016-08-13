(set-logic QF_S)

(declare-fun a0 () String)
(declare-fun a1 () String)
(declare-fun a2 () String)

(assert
(and

(= a0 "")
(= a1 "a")
(< a0 a1)

))
(check-sat)

