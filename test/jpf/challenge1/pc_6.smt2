(declare-fun in_1 () String)

(assert (< 1 (len in_1)))
(assert (not (= (indexOf "" (concat "" (charAt in_1 0))) (- 1))))
(assert (< 0 (len in_1)))
(check-sat)