(declare-fun v1 () String)
(declare-fun v2 () Int)
(declare-fun v3 () Int)

(assert (or
          (and (str.contains v1 "<") (< v3 v2) ) 
          (and (str.contains v1 ">") )
        )
)


(check-sat)
