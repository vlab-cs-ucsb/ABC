(set-logic QF_S)

(declare-fun var_abc () Int)

(assert (= 3 (+ var_abc var_abc var_abc)))

(check-sat)

