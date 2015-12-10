; introduces let binding 
(declare-fun abc () String)

(assert (= (indexOf abc "a" (indexOf abc "/" (indexOf abc " "))) 5) )

(check-sat)

