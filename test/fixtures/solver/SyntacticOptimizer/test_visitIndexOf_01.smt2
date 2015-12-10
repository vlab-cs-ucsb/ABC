; introduces let binding 
(declare-fun abc () String)

(assert (= (indexOf abc "/" (indexOf abc " ")) 5) )

(check-sat)

