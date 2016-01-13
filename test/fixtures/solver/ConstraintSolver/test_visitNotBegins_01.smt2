(set-logic QF_S)

(declare-fun var_abc () String)

(assert (notBegins var_abc "a" ))

(check-sat)

