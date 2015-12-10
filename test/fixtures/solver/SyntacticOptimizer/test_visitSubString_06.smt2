; introduces let binding 
(declare-fun abc () String)

(assert (= (subString abc (indexOf abc "/" 5)) "abc") )

(check-sat)

