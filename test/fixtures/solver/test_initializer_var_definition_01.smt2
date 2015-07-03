(set-logic QF_S)

(declare-fun abc () Int)
(declare-fun def () Int)
(declare-fun abc () String)

(assert (= abc def))

(check-sat)

