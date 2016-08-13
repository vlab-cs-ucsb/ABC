(set-logic QF_S)

(declare-fun secret () String)
(declare-fun public () String)
(assert
(and

(begins secret "id=")
(begins secret public)

))
(check-sat)

