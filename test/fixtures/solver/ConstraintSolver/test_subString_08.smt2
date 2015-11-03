(set-logic QF_S)

(declare-fun var_abc () String)
(declare-fun tmp () String)

(assert (= tmp /(abc|xyz)/))
(assert (= var_abc (subString tmp 1)))

(check-sat)

