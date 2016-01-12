(set-logic QF_S)

(declare-fun var_abc () String)

(assert (notContains var_abc "a" ))

(check-sat)

