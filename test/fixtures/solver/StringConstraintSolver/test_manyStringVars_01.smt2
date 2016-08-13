(set-logic QF_S)

(declare-fun a0 () String)
(declare-fun a1 () String)
(declare-fun a2 () String)
(declare-fun a3 () String)
(declare-fun a4 () String)
(declare-fun a5 () String)
(declare-fun a6 () String)
(declare-fun a7 () String)
(declare-fun a8 () String)
(declare-fun a9 () String)

(declare-fun a10 () String)
(declare-fun a11 () String)
(declare-fun a12 () String)
(declare-fun a13 () String)
(declare-fun a14 () String)
(declare-fun a15 () String)
(declare-fun a16 () String)
(declare-fun a17 () String)
(declare-fun a18 () String)
(declare-fun a19 () String)

(assert (and
(!= a0 a1)
(!= a1 a2)


))

(check-sat)

