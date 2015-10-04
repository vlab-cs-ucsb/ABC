(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (lastIndexOf var_abc "a") 2))

(check-sat)

