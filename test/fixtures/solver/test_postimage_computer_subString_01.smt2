(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (subString "abc" 1)))

(check-sat)

