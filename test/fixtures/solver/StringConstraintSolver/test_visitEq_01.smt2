(set-logic QF_S)

(declare-fun a0 () String)
(declare-fun a1 () String)
(declare-fun a2 () String)

(assert
(and

(= a1 (concat a0 "zebra"))
(= a2 (concat a0 "giraffe"))
(!= a1 a2)

))
(check-sat)

