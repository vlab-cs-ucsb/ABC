(set-logic QF_S)

(declare-fun secret () String)
(declare-fun public () String)
(declare-fun result () String)

(assert
(and


(not (begins secret public))

;(= result (concat "id=" secret))
;(begins result public)
;(begins public "id=")
(in secret /([0-9])+/)
(in public /([0-9])+/)
;(= (len secret) 5)

))
(check-sat)

