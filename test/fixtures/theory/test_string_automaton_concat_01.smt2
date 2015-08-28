(set-logic QF_S)

(declare-fun var_abc () String)

;(assert (= var_abc (concat "a" "b")))
;(assert (= var_abc (concat "a" /(bc)+/)))
;(assert (= var_abc (concat "" /(bc)+/)))
;(assert (= var_abc (concat /(bc)+/ "")))
;(assert (= var_abc (concat "a" /(bc)*/)))
; compare /b*c/ with /db*c/ to resolve the issue
(assert (= var_abc (concat /a/ /db*c/)))

(check-sat)

