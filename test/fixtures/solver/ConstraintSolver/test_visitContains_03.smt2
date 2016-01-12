(set-logic QF_S)

(declare-fun var_abc () String)

(assert (contains "abc" var_abc ))

(check-sat)