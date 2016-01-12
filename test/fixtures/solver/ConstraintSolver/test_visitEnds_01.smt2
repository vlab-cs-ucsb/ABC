(set-logic QF_S)

(declare-fun var_abc () String)

(assert (ends var_abc "a" ))

(check-sat)

