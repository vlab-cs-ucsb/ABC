(set-logic QF_S)

(declare-fun var_abc () Int)

(assert (= var_abc (len "baki")))

(check-sat)

