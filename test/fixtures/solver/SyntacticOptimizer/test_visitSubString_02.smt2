; introduces let binding 
(declare-fun abc () String)

(assert (= (subString abc (lastIndexOf abc "/" (lastIndexOf abc " "))) "abc") )

(check-sat)

