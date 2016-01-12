(set-logic QF_S)

(declare-fun var_abc () String)

(assert (notContains "abc" var_abc ))

(check-sat)