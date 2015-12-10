; introduces let binding 
(declare-fun abc () String)

(assert (= (subString abc (indexOf abc "/" (lastIndexOf abc " "))) "abc") )

(check-sat)

