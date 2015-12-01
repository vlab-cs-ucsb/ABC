(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= (lastIndexOf /cb*a+/ /b*/) 2))

(check-sat)


