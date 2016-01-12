(set-logic QF_S)

(declare-fun var_abc () String)

(assert (ends "abc" var_abc ))

(check-sat)