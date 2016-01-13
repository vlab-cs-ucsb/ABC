(set-logic QF_S)

(declare-fun var_abc () String)

(assert (notEnds "abc" var_abc ))

(check-sat)