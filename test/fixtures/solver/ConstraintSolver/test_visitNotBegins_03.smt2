(set-logic QF_S)

(declare-fun var_abc () String)

(assert (notBegins "abc" var_abc ))

(check-sat)