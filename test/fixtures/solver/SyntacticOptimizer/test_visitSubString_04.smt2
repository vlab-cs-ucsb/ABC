; introduces let binding 
(declare-fun abc () String)

(assert (= (subString abc (indexOf abc "/" (indexOf abc " "))) "abc") )

(check-sat)

