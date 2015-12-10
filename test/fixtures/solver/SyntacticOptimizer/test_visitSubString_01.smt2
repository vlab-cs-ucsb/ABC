; introduces let binding 
(declare-fun abc () String)

(assert (= (subString abc (lastIndexOf abc "/" (indexOf abc " "))) "abc") )

(check-sat)

