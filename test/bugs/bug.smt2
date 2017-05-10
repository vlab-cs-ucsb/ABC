(declare-fun v () String)
(declare-fun i () Int)
(declare-fun j () Int)

(assert (= i (* 2 j)))
(assert (= (str.at v i) "a" ))

(check-sat)
