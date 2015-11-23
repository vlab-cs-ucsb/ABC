(set-logic QF_S)

(declare-fun x () Int)
(declare-fun str () String)

(assert (= x 0))
(assert (>= (+ x (len str)) 0))
;(assert (= str /(cde)*/))
;(assert (= str /cdedd(de)+/))
;(assert (= str /a{3,3}|a{5,5}(de)+/))
;(assert (= str /(baaabab)+/)) ; 7 + 7k
;(assert (= str /a{7,7}|a{7,7}(a{14,14})+/)) ; 7 + 14k case
(assert (= str /a{14,14}|a{28,28}|a{14,14}(a{28,28})+|a{28,28}(a{35,35})+/)) ; 14 + 28k, 28 + 35k case
;(assert (= str /aaaaaaaa(aaa)*|aaaaaaaa(aaaa)*/))
;(assert (= str /(aa)|(bbb)+/))
;(assert (= str /(aaaaa)+|b(aaaa)+/))
;(assert (= str /aaaaaaa|a{0,5}/))
;(assert (= str /(aaaaaaa)+|aa|aaa|aaaaa/))
(check-sat)