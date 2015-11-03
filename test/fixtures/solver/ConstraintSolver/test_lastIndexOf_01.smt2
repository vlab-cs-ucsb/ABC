(set-logic QF_S)

(declare-fun var_abc () Int)

(assert (= var_abc (lastIndexOf /(abcb|debfbg)/ "b")))

(check-sat)

