(set-logic QF_S)

(declare-fun a () String)

(assert (begins  a "b" ))

(check-sat)

