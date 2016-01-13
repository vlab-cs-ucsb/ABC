(set-logic QF_S)

(declare-fun var_abc () String)

(assert (notEnds var_abc "a" ))

(check-sat)

