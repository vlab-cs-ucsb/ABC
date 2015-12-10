; introduces let binding 
(declare-fun abc () String)

(assert (= (subString abc (lastIndexOf abc "/" 5)) "abc") )

(check-sat)

