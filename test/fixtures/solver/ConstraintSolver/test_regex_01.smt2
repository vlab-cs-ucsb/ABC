(set-logic QF_S)

(declare-fun var_abc () String)

(assert (= var_abc (concat /a/ /b*c/)))
;(assert (= var_abc (concat /ab*/ /c/)))
;(assert (= var_abc /(b*c|b*)/ ))
;(assert (= var_abc (concat "" /b*c/)))
;(assert (= var_abc (concat /b*c/ /a*/)))

(check-sat)

