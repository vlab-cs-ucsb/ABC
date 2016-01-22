(declare-fun in_1 () String)

;(assert (> (len (concat (concat (concat (concat (concat "~" (indexOf "" (concat "" (charAt in_1 0)))) "~") (len (concat "" (charAt in_1 0)))) "~") (charAt in_1 1))) (len (concat (concat "" (concat "" (charAt in_1 0))) (charAt in_1 1)))))
(assert (= (indexOf "" (concat (concat "" (concat "" (charAt in_1 1))) (charAt in_1 1))) (- 1)))
;(assert (< 1 (len in_1)))
;(assert (not (= (indexOf "" (concat "" (charAt in_1 0))) (- 1))))
;(assert (< 0 (len in_1)))
(check-sat)