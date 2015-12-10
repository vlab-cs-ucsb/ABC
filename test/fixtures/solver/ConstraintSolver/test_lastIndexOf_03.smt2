(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (lastIndexOf var_abc /baki/) 5))

(check-sat)

