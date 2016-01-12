(set-logic QF_S)

(declare-fun var_abc () String)

(assert (begins var_abc "a" ))

(check-sat)

