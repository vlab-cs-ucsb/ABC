(declare-fun in_1 () String)

(assert (=  "" (concat "" (charAt in_1 0))) )
(check-sat)
