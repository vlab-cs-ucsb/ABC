(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun p () String)

(assert (and 

(= (concat "alpha" z "beta") (concat x y))
(<= x z)
;(<= z p)

))
