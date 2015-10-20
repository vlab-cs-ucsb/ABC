(set-logic QF_S)

(declare-fun var_abc () Int)

(assert  (= (- var_abc 5) 3))

(check-sat)
