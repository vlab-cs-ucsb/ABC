(declare-fun in_1 () String)

(assert (<= (len (concat "~0~0~" (charAt in_1 0))) (len (concat "" (charAt in_1 0)))))
(assert (< 0 (len in_1)))
(check-sat)